"""
RWMod Repacker - Input Validation + RWMod Validator

GUI:
  Source field   -> can be a FOLDER (for Repack) or an .rwmod FILE (for Validate)
  Browse buttons -> Folder or File - both write to Source
  Repack         -> packs a folder into .rwmod
  Validate       -> checks an .rwmod file (clean or protected)
"""

from __future__ import annotations

import hashlib
import hmac
import io
import mmap
import os
import random
import shutil
import string
import struct
import tempfile
import threading
import time
import zipfile

import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext
from typing import Callable, Optional, Union


# ===========================================================================
# CONFIG
# ===========================================================================
LAYERS        = 13
MIN_JUNK_SIZE = 11_392
MAX_JUNK_SIZE = 11_584

EOCD_SIG        = b"PK\x05\x06"
CD_SIG          = b"PK\x01\x02"
EOCD_SIZE       = 22
N_FAKE_EOCD     = 100
FAKE_TRAIL_JUNK = (4_096, 12_288)

SIG_LFH   = b"PK\x03\x04"
SIG_RWMOD = b"RWMOD"
SIG_LAYER = b"DRGN"
SIG_RWF   = b"RWF"
SIG_LOCK  = b"LOCK"
SIG_HDR   = b"HDR_"
SIG_SIG   = b"SIG_"
SIG_FTR   = b"FTR_"

TEMP_SUFFIX = ".part"

MMAP_THRESHOLD  = 64 * 1024 * 1024
CHUNK_SIZE      = 1 * 1024 * 1024
RANDOM_BUF_SIZE = 64 * 1024
_RANDOM_BUF     = os.urandom(RANDOM_BUF_SIZE)

EXCLUDE_DIRS  = {".git", ".svn", ".hg", "__pycache__", ".idea", ".vscode"}
EXCLUDE_FILES = {".DS_Store", "Thumbs.db", "desktop.ini"}

INCOMPRESSIBLE_EXTS = {
    ".png", ".jpg", ".jpeg", ".gif", ".webp", ".bmp",
    ".ogg", ".mp3", ".wav", ".flac", ".m4a", ".aac",
    ".zip", ".rwmod", ".gz", ".7z", ".rar", ".xz", ".bz2",
    ".mp4", ".webm", ".mkv", ".mov", ".avi",
}

STAGE_WEIGHTS = {
    "zip":       (0,  40),
    "layers":    (40, 60),
    "copy":      (60, 90),
    "fake_eocd": (90, 95),
    "finalize":  (95, 100),
}


# ===========================================================================
# HELPERS
# ===========================================================================
def pack_chunk(tag: bytes, payload: bytes) -> bytes:
    return tag + len(payload).to_bytes(4, "big") + payload


def write_random(out, n: int) -> None:
    while n > 0:
        take = min(n, RANDOM_BUF_SIZE)
        out.write(_RANDOM_BUF[:take])
        n -= take


def u16(b, o): return struct.unpack_from("<H", b, o)[0]
def u32(b, o): return struct.unpack_from("<I", b, o)[0]


def find_all_eocds(data: bytes) -> list[int]:
    out = []
    i = 0
    while True:
        j = data.find(EOCD_SIG, i)
        if j < 0:
            break
        out.append(j)
        i = j + 1
    return out


def parse_eocd(data: bytes, pos: int) -> Optional[dict]:
    if pos + EOCD_SIZE > len(data):
        return None
    return {
        "pos":          pos,
        "disk_num":     u16(data, pos + 4),
        "cd_start_dk":  u16(data, pos + 6),
        "entries_dk":   u16(data, pos + 8),
        "entries_all":  u16(data, pos + 10),
        "cd_size":      u32(data, pos + 12),
        "cd_offset":    u32(data, pos + 16),
        "comment_len":  u16(data, pos + 20),
    }


# ===========================================================================
# FAKE EOCD BLOCK BUILDER
# ===========================================================================
def _fake_cd_entry(rng: random.Random) -> bytes:
    """
    One syntactically well-formed central directory file header (the fixed
    46-byte record per the ZIP spec) with garbage content but a precisely
    known total length. A real parser will accept it as entry #1 without
    complaint -- the giveaway only shows up when it goes looking for
    entry #2 right after it.
    """
    filename_len = rng.randint(4, 20)
    h = bytearray(46)
    h[0:4]   = CD_SIG
    h[4:6]   = rng.randint(0, 63).to_bytes(2, "little")      # version made by
    h[6:8]   = rng.randint(10, 63).to_bytes(2, "little")     # version needed
    h[8:10]  = rng.randint(0, 2047).to_bytes(2, "little")    # flags
    h[10:12] = rng.choice([0, 8]).to_bytes(2, "little")      # compression method
    h[12:14] = rng.randint(0, 0xFFFF).to_bytes(2, "little")  # mod time
    h[14:16] = rng.randint(0x21, 0xFFFF).to_bytes(2, "little")  # mod date
    h[16:20] = os.urandom(4)                                  # CRC-32
    h[20:24] = rng.randint(0, 1_000_000).to_bytes(4, "little")  # compressed size
    h[24:28] = rng.randint(0, 1_000_000).to_bytes(4, "little")  # uncompressed size
    h[28:30] = filename_len.to_bytes(2, "little")
    h[30:32] = (0).to_bytes(2, "little")   # extra field length
    h[32:34] = (0).to_bytes(2, "little")   # comment length
    h[34:36] = (0).to_bytes(2, "little")   # disk number start
    h[36:38] = (0).to_bytes(2, "little")   # internal attrs
    h[38:42] = os.urandom(4)               # external attrs
    h[42:46] = os.urandom(4)               # local header offset
    return bytes(h) + os.urandom(filename_len)


def build_fake_eocd_block(n_fakes: int, rng: random.Random,
                          block_start_offset: int) -> bytes:
    block = bytearray()

    def vary_comment_len() -> int:
        bucket = rng.randint(0, 2)
        if bucket == 0:
            return rng.randint(4, 40)
        elif bucket == 1:
            return rng.randint(100, 500)
        else:
            return rng.randint(1000, 3000)

    for _ in range(n_fakes):
        # Real zips lay out [central directory][EOCD] -- CD first, EOCD right
        # after it. We mirror that ordering exactly so the size/offset math
        # is genuinely self-consistent, not just plausible-looking: a reader
        # that trusts the EOCD's arithmetic will confidently locate what
        # looks like a real central directory. One well-formed-but-garbage
        # entry parses cleanly, but cd_size is deliberately set larger than
        # that one entry consumes, so the parser goes looking for a second
        # entry immediately after it -- landing on plain junk instead of a
        # signature. That's a guaranteed "bad magic number" failure, the
        # same signature as an ordinarily corrupted zip, not an EOCD that's
        # obviously impossible on its face.
        cd_relative_pos = len(block)
        cd_absolute_pos = block_start_offset + cd_relative_pos
        block.extend(_fake_cd_entry(rng))
        block.extend(os.urandom(rng.randint(16, 64)))

        eocd_pos = len(block)
        cd_size  = eocd_pos - cd_relative_pos
        block.extend(EOCD_SIG)
        block.extend(b"\x00" * 18)

        block[eocd_pos + 4 : eocd_pos + 6]   = rng.randint(0, 1).to_bytes(2, "little")
        block[eocd_pos + 6 : eocd_pos + 8]   = rng.randint(0, 1).to_bytes(2, "little")
        block[eocd_pos + 8 : eocd_pos + 10]  = rng.randint(2, 50).to_bytes(2, "little")
        block[eocd_pos + 10:eocd_pos + 12]   = rng.randint(2, 50).to_bytes(2, "little")
        block[eocd_pos + 12:eocd_pos + 16]   = cd_size.to_bytes(4, "little")
        block[eocd_pos + 16:eocd_pos + 20]   = cd_absolute_pos.to_bytes(4, "little")
        comment_len = vary_comment_len()
        block[eocd_pos + 20:eocd_pos + 22]   = comment_len.to_bytes(2, "little")
        block.extend(os.urandom(comment_len))

        block.extend(os.urandom(rng.randint(16, 48)))

    block.extend(os.urandom(rng.randint(*FAKE_TRAIL_JUNK)))
    return bytes(block)


# ===========================================================================
# VALIDATION LOGIC
# ===========================================================================
def try_eocd(data: bytes, eocd_pos: int, eocd: dict) -> tuple[bool, object]:
    """
    Try to open the ZIP using this EOCD candidate.
    Returns (True, namelist) on success, (False, reason_str) on failure.
    """
    cd_size   = eocd["cd_size"]
    cd_offset = eocd["cd_offset"]

    # Standard interpretation: cd_offset is relative to archive start
    archive_start = eocd_pos - cd_size - cd_offset
    if archive_start < 0:
        return False, "archive start would be negative"

    cd_in_file = archive_start + cd_offset
    if cd_in_file + 4 > len(data):
        return False, "CD position past EOF"
    if data[cd_in_file:cd_in_file + 4] != CD_SIG:
        return False, "no PK\\x01\\x02 at computed CD position"

    eocd_end = eocd_pos + EOCD_SIZE + eocd["comment_len"]
    if eocd_end > len(data):
        return False, "EOCD end past EOF"

    try:
        blob = data[archive_start:eocd_end]
        with zipfile.ZipFile(io.BytesIO(blob)) as zf:
            names = zf.namelist()
            return True, names
    except Exception as e:
        return False, str(e)[:80]


def validate_rwmod_report(path: str) -> tuple[str, bool]:
    """Run a full validation report. Returns (report_text, is_valid)."""
    with open(path, "rb") as f:
        data = f.read()

    lines = []
    lines.append(f"File:    {path}")
    lines.append(f"Size:    {len(data):,} bytes ({len(data) / 1_048_576:.2f} MB)")
    lines.append("")

    lfh  = data.count(SIG_LFH)
    cd   = data.count(CD_SIG)
    eocd = data.count(EOCD_SIG)
    lines.append("Signature counts:")
    lines.append(f"   PK\\x03\\x04 (LFH):   {lfh:,}")
    lines.append(f"   PK\\x01\\x02 (CD):    {cd:,}")
    lines.append(f"   PK\\x05\\x06 (EOCD):  {eocd:,}")
    lines.append("")

    eocd_positions = find_all_eocds(data)
    if not eocd_positions:
        lines.append("=" * 55)
        lines.append("VERDICT: INVALID - no EOCD signatures found")
        lines.append("=" * 55)
        lines.append("")
        lines.append("This file is NOT a valid .rwmod / ZIP.")
        lines.append("It will NOT load in Rusted Warfare.")
        return "\n".join(lines), False

    lines.append(f"Testing {len(eocd_positions)} EOCD candidate(s) (last -> first)...")
    lines.append("")

    real_eocd_pos  = None
    real_eocd_info = None
    names          = None
    fakes_skipped  = 0

    for idx, pos in enumerate(reversed(eocd_positions), start=1):
        e = parse_eocd(data, pos)
        if e is None:
            fakes_skipped += 1
            continue

        ok, result = try_eocd(data, pos, e)
        if ok:
            real_eocd_pos  = pos
            real_eocd_info = e
            names          = result
            lines.append(f"   Candidate #{idx} (byte {pos:,}) -> VALID")
            break
        else:
            fakes_skipped += 1
            if idx <= 3:
                lines.append(f"   Candidate #{idx} (byte {pos:,}) -> {result}")
            elif idx == 4:
                remaining = len(eocd_positions) - 3
                lines.append(f"   ... skipping remaining {remaining} candidate(s) ...")

    lines.append("")

    if real_eocd_pos is None:
        lines.append("=" * 55)
        lines.append("VERDICT: INVALID")
        lines.append("=" * 55)
        lines.append(f"Tested {len(eocd_positions)} EOCD(s) - none produced a valid ZIP.")
        lines.append("This file will NOT load in Rusted Warfare.")
        return "\n".join(lines), False

    lines.append("=" * 55)
    lines.append("VERDICT: VALID")
    lines.append("=" * 55)
    lines.append(f"Real EOCD position:    byte {real_eocd_pos:,}")
    lines.append(f"CD offset:             {real_eocd_info['cd_offset']:,}")
    lines.append(f"CD size:               {real_eocd_info['cd_size']:,}")
    lines.append(f"Entries:               {len(names)}")
    lines.append(f"Fake EOCDs skipped:    {fakes_skipped}")
    lines.append("")

    if fakes_skipped > 0:
        lines.append(f"PROTECTED - {fakes_skipped} fake EOCD(s) detected.")
        lines.append("   External tools (7-Zip, WinRAR, extractors) will fail.")
        lines.append("   Rusted Warfare should still load this file.")
    else:
        lines.append("CLEAN - no fake EOCDs detected.")

    lines.append("")
    lines.append("First entries in archive:")
    for n in names[:12]:
        lines.append(f"   - {n}")
    if len(names) > 12:
        lines.append(f"   ... and {len(names) - 12} more")

    return "\n".join(lines), True


# ===========================================================================
# OBFUSCATION PRIMITIVES
# ===========================================================================
def get_header_sig(file_data: Optional[bytes] = None) -> bytes:
    if file_data:
        seed = hashlib.sha3_512(file_data).digest()[:16]
    else:
        seed = os.urandom(16)
    rng = random.Random(int.from_bytes(seed, "big"))

    patterns = [
        lambda: bytes([rng.randint(0x80, 0xFF), 0x50 + rng.randint(0, 15),
                       0x4E + rng.choice([0, 1, -1]), rng.choice([0x47, 0x46, 0x48]),
                       0x0D, 0x0A, rng.choice([0x1A, 0x1B, 0x1C]),
                       rng.choice([0x00, 0x0A, 0xFF])]),
        lambda: bytes([0x50, 0x4B, rng.choice([0x03, 0x05, 0x07]), 0x04,
                       rng.randint(0x10, 0x20), 0x00, 0x00,
                       rng.choice([0x08, 0x00])]),
        lambda: bytes([rng.randint(0x80, 0xEF), rng.randint(0x20, 0x7F),
                       rng.randint(0x00, 0x1F), rng.randint(0xC0, 0xFF),
                       rng.choice([0x00, 0xFF]), rng.randint(0x10, 0xF0)]),
        lambda: bytes([0x25, 0x50, 0x44, 0x46, 0x2D,
                       rng.choice([0x31, 0x32, 0x33, 0x34]), 0x2E,
                       rng.choice([0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]),
                       0x0A, 0x25,
                       rng.choice([0xE2, 0xE3, 0xE4, 0xE5]),
                       rng.randint(0x80, 0xFF), rng.randint(0x80, 0xFF)]),
        lambda: bytes([0x47, 0x49, 0x46, 0x38,
                       rng.choice([0x37, 0x39, 0x61]),
                       0x00, 0x01,
                       rng.randint(0x02, 0x08), 0x00,
                       rng.choice([0xF0, 0x80, 0x90]),
                       rng.randint(0x00, 0x07),
                       rng.choice([0x00, 0x21, 0x2C])]),
    ]

    header = bytearray(rng.choice(patterns)())

    def mutate_byte(b: int) -> int:
        b ^= 0xFF
        b = (b + rng.randint(1, 255)) % 256
        b = (b - rng.randint(1, 255)) % 256
        b = (b * rng.randint(2, 255)) % 256
        b = (b // rng.randint(1, 255)) % 256
        b = rng.randint(0, 255)
        return b

    for _ in range(5):
        pos = rng.randint(0, len(header) - 1)
        header[pos] = mutate_byte(header[pos])

    trailer_len = rng.randint(2, 8)
    trailer = bytearray([rng.randint(0, 255) for _ in range(trailer_len)])
    for i in range(len(trailer)):
        for _ in range(5):
            trailer[i] = mutate_byte(trailer[i])

    if rng.random() > 0.7:
        insert_pos = rng.randint(1, len(header) - 1)
        header = header[:insert_pos] + trailer + header[insert_pos:]
    else:
        header += trailer

    return bytes(header)


def get_footer_sig(file_data: Optional[bytes] = None) -> bytes:
    if file_data:
        seed = hashlib.sha3_512(file_data).digest()[:16]
    else:
        seed = os.urandom(16)
    rng = random.Random(int.from_bytes(seed, "big"))

    patterns = [
        lambda: (
            "".join(rng.choices(string.ascii_letters + string.digits, k=rng.randint(8, 16))).encode("ascii")
            + rng.choice([b"--", b"~~", b"||", b"::", b"$$"])
            + bytes([rng.randint(32, 126) for _ in range(rng.randint(8, 16))])
            + rng.choice([b"\x00\x00", b"\xFF\xFF", b"\xFE\xFE", b"\x01\x01"])
        ),
        lambda: (
            bytes([rng.randint(0x80, 0xFF) for _ in range(rng.randint(6, 12))])
            + bytes([rng.randint(0x00, 0x7F) for _ in range(rng.randint(4, 8))])
            + rng.choice([b"\x55\xAA", b"\xAA\x55", b"\xC3\x3C"])
        ),
    ]

    footer = bytearray(rng.choice(patterns)())
    mutations = ["xor", "swap", "rotate", "multiply_mod", "divide_mod", "insert"]
    rng.shuffle(mutations)

    for mutation in mutations:
        if mutation == "xor":
            for pos in range(len(footer)):
                footer[pos] ^= 0xFF
        elif mutation == "swap":
            for pos in range(len(footer) - 1):
                footer[pos], footer[pos + 1] = footer[pos + 1], footer[pos]
        elif mutation == "rotate":
            for pos in range(len(footer)):
                shift = rng.randint(1, 7)
                footer[pos] = ((footer[pos] << shift) | (footer[pos] >> (8 - shift))) & 0xFF
        elif mutation == "multiply_mod":
            mul = rng.randint(2, 15)
            for pos in range(len(footer)):
                footer[pos] = (footer[pos] * mul) % 256
        elif mutation == "divide_mod":
            div = rng.randint(2, 15)
            for pos in range(len(footer)):
                footer[pos] = (footer[pos] // div) % 256
        elif mutation == "insert":
            new_footer = bytearray()
            for pos in range(len(footer)):
                new_footer.append(footer[pos])
                if len(new_footer) < 100 and rng.random() < 0.2:
                    new_footer.append(rng.randint(0, 255))
            footer = new_footer

    return bytes(footer)


def mutable_signature(base: Union[bytes, str], seed: Optional[bytes] = None,
                      heavy: bool = True) -> bytes:
    if seed:
        rng = random.Random(int.from_bytes(seed, "big"))
    else:
        rng = random.Random()

    base_bytes = base.encode("utf-8") if isinstance(base, str) else base
    base_hash = hashlib.sha256(base_bytes).digest()
    noise_len = (base_hash[0] % 32) + 16

    np = rng.randint(0, 3)
    if np == 0:
        noise = bytes([rng.randint(0, 255) for _ in range(noise_len)])
    elif np == 1:
        chars = string.ascii_letters + string.digits + string.punctuation
        noise = "".join(rng.choices(chars, k=noise_len)).encode("ascii")
    elif np == 2:
        start = rng.randint(0, 255)
        step = rng.choice([1, -1, 2, -2, 5])
        noise = bytes([(start + i * step) % 256 for i in range(noise_len)])
    else:
        key = rng.randint(1, 255)
        base_val = rng.randint(0, 255)
        noise = bytes([(base_val + i) % 256 ^ key for i in range(noise_len)])

    ip = rng.randint(0, len(base_bytes))
    if rng.random() > 0.5:
        sig = bytearray(base_bytes[:ip] + noise + base_bytes[ip:])
    else:
        nb = noise[:rng.randint(0, len(noise))]
        na = noise[len(nb):]
        sig = bytearray(nb + base_bytes + na)

    passes = rng.randint(8, 15) if heavy else rng.randint(3, 6)
    for _ in range(passes):
        t = rng.randint(0, 9)
        pos = rng.randint(0, len(sig) - 1)

        if t == 0:
            sig[pos] ^= rng.randint(1, 255)
        elif t == 1:
            if len(sig) > 4:
                s = rng.randint(0, len(sig) - 2)
                e = min(len(sig), s + rng.randint(2, 8))
                ch = sig[s:e]; ch.reverse(); sig[s:e] = ch
        elif t == 2:
            sh = rng.randint(1, 7)
            sig[pos] = ((sig[pos] << sh) | (sig[pos] >> (8 - sh))) & 0xFF
        elif t == 3:
            sh = rng.randint(1, 7)
            sig[pos] = ((sig[pos] >> sh) | (sig[pos] << (8 - sh))) & 0xFF
        elif t == 4:
            if len(sig) < 256:
                sig.insert(pos, rng.randint(0, 255))
        elif t == 5:
            if len(sig) > 8:
                del sig[pos]
        elif t == 6:
            f = rng.randint(2, 15)
            sig[pos] = (sig[pos] * f) % 256
        elif t == 7:
            d = rng.randint(1, 15)
            sig[pos] = (sig[pos] // d) % 256
        elif t == 8:
            if len(sig) > 12:
                sz = rng.randint(3, 6)
                i = rng.randint(0, len(sig) - sz)
                j = rng.randint(0, len(sig) - sz)
                if i != j:
                    a = sig[i:i + sz]; b = sig[j:j + sz]
                    sig[i:i + sz], sig[j:j + sz] = b, a
        else:
            fr = hashlib.md5(sig).digest()
            sig[pos] = fr[rng.randint(0, len(fr) - 1)]

    if heavy and len(sig) > 32:
        rng.shuffle(sig)
    return bytes(sig)


def polymorphic_encoder(data: bytes, seed: bytes) -> bytes:
    rng = random.Random(int.from_bytes(seed, "big"))
    key_len = 2 + (int.from_bytes(seed[:1], "big") % 7)
    key = hashlib.sha256(seed).digest()[:key_len]
    x = bytearray(b ^ key[i % key_len] for i, b in enumerate(data))

    bs = [2, 4, 8][seed[1] % 3]
    sh_stage = bytearray()
    for i in range(0, len(x), bs):
        block = bytearray(x[i:i + bs])
        if (seed[i % len(seed)] & 1) == 0:
            block.reverse()
        else:
            rng.shuffle(block)
        sh_stage.extend(block)

    kv = (seed[2] % 254) + 1
    a = bytearray((b + kv) % 256 if (b & 1) else (b - kv) % 256 for b in sh_stage)

    s1 = (seed[3] % 7) + 1
    r = bytearray(((b << s1) | (b >> (8 - s1))) & 0xFF for b in a)

    fk = (seed[4] % 254) + 1
    s1b = bytearray(b ^ fk for b in r)

    s2 = (seed[5] % 7) + 1
    s2b = bytearray(((b << s2) | (b >> (8 - s2))) & 0xFF for b in s1b)

    bs2 = [2, 4][seed[6] % 2]
    out = bytearray()
    for i in range(0, len(s2b), bs2):
        block = s2b[i:i + bs2]
        out.extend(block[::-1])
    return bytes(out)


def derive_ephemeral_key(seed: bytes) -> bytes:
    """
    Multi-stage key derivation that mixes a content-derived seed with
    entropy that is never recoverable from the seed itself (PID,
    nanosecond timestamp, fresh os.urandom). Unlike a key derived purely
    from `seed`, this key cannot be reconstructed by anyone -- even
    someone who has already recovered the real archive content -- because
    the ephemeral entropy that fed it only ever existed for this one call.
    """
    entropy = f"{os.getpid()}-{time.time_ns()}-{os.urandom(16).hex()}".encode()
    d1 = hashlib.sha3_512(seed + entropy).digest()
    d2 = hashlib.blake2b(d1, digest_size=32).digest()
    d3 = hashlib.shake_256(d2).digest(32)

    rng = random.Random(int.from_bytes(d3[:16], "big"))
    key = bytearray(d3)
    mask = rng.randint(1, 255)
    xor_k = d2[rng.randint(0, len(d2) - 1)]
    for i in range(len(key)):
        key[i] ^= mask
        key[i] ^= xor_k
        key[i] = ((key[i] << 1) | (key[i] >> 7)) & 0xFF
    rng.shuffle(key)

    tag = hmac.new(d1, key, hashlib.sha3_256).digest()[:8]
    return bytes(key) + tag


def encrypt_with_chaff(real_data: bytes, seed: bytes) -> bytes:
    rng = random.Random(int.from_bytes(hashlib.blake2b(seed, digest_size=16).digest(), "big"))
    data = bytearray(real_data)

    for _ in range(rng.randint(10, 30)):
        pos = rng.randint(0, len(data))
        cl = rng.randint(2, 16)
        cd = os.urandom(cl)
        salted = hashlib.sha3_256(seed + cd).digest()[:cl]
        mixed = bytes(a ^ b for a, b in zip(cd, salted))
        data[pos:pos] = mixed

    secret = derive_ephemeral_key(seed)
    ks = hashlib.shake_256(secret).digest(len(data))
    enc = bytearray(len(data))
    for i, b in enumerate(data):
        enc[i] = b ^ ks[i]
    tag = hmac.new(secret, enc, hashlib.blake2s).digest()[:16]
    enc.extend(tag)
    return bytes(enc)


def create_obfuscation_layers(content_hash_seed: bytes) -> bytes:
    rng = random.Random(int.from_bytes(content_hash_seed, "big"))
    layers = bytearray()
    mode_key = b"OBFUSCATION_KEY"

    for i in range(LAYERS):
        layer_seed = hashlib.sha3_256(f"{content_hash_seed}-layer-{i}".encode()).digest()

        fake_header = SIG_LFH + os.urandom(rng.randint(64, 256))
        misaligned = os.urandom(rng.randint(128, 512))
        layers.extend(pack_chunk(SIG_LAYER, fake_header + misaligned))

        for _ in range(rng.randint(3, 6)):
            fake_rwmod = SIG_RWMOD + os.urandom(rng.randint(60, 140))
            sig = mutable_signature(mode_key, layer_seed)
            layers.extend(pack_chunk(SIG_RWF, fake_rwmod + sig))

        trap = polymorphic_encoder(os.urandom(256), layer_seed)
        layers.extend(pack_chunk(SIG_LOCK, trap))

    final_hash = hashlib.sha512(layers).digest()
    return bytes(layers) + final_hash


# ===========================================================================
# FOLDER SCAN
# ===========================================================================
class FolderReport:
    def __init__(self):
        self.total_files: int = 0
        self.total_bytes: int = 0
        self.has_mod_info: bool = False
        self.mod_info_size: int = 0
        self.top_level_files: list[str] = []
        self.warnings: list[str] = []

    def summary(self) -> str:
        lines = []
        lines.append(f"Total files:  {self.total_files:,}")
        lines.append(f"Total size:   {self.total_bytes:,} bytes "
                     f"({self.total_bytes / 1_048_576:.2f} MB)")
        lines.append(f"mod-info.txt: "
                     f"{'present (' + str(self.mod_info_size) + ' bytes)' if self.has_mod_info else 'MISSING'}")
        if self.top_level_files:
            lines.append("")
            lines.append("Top-level contents:")
            for name in self.top_level_files[:15]:
                lines.append(f"  - {name}")
            if len(self.top_level_files) > 15:
                lines.append(f"  ... and {len(self.top_level_files) - 15} more")
        if self.warnings:
            lines.append("")
            lines.append("WARNINGS:")
            for w in self.warnings:
                lines.append(f"  - {w}")
        return "\n".join(lines)


def scan_folder(folder_path: str) -> FolderReport:
    rpt = FolderReport()
    if not os.path.isdir(folder_path):
        rpt.warnings.append(f"Not a directory: {folder_path}")
        return rpt

    seen_dirs: set[tuple[int, int]] = set()
    for root, dirs, files in os.walk(folder_path, followlinks=False):
        try:
            st = os.stat(root)
            key = (st.st_dev, st.st_ino)
            if key in seen_dirs:
                dirs[:] = []
                continue
            seen_dirs.add(key)
        except OSError:
            continue

        dirs[:] = [d for d in dirs if d not in EXCLUDE_DIRS and not d.startswith(".")]

        for f in files:
            if f in EXCLUDE_FILES or f.startswith("."):
                continue
            full = os.path.join(root, f)
            try:
                size = os.path.getsize(full)
            except OSError:
                continue
            rpt.total_files += 1
            rpt.total_bytes += size

            rel = os.path.relpath(full, folder_path)
            if os.sep not in rel and rel.lower() == "mod-info.txt":
                rpt.has_mod_info = True
                rpt.mod_info_size = size

    try:
        for name in sorted(os.listdir(folder_path))[:20]:
            rpt.top_level_files.append(name)
    except OSError:
        pass

    if rpt.total_files == 0:
        rpt.warnings.append("Folder is empty (no files to pack).")
    if not rpt.has_mod_info:
        rpt.warnings.append(
            "mod-info.txt not found at the top level. "
            "Rusted Warfare may reject this mod."
        )
    return rpt


# ===========================================================================
# ZIP + PACKING
# ===========================================================================
def zip_folder(folder_path: str, zip_path: str,
               callback: Optional[Callable[[float], None]] = None) -> bytes:
    if not os.path.isdir(folder_path):
        raise FileNotFoundError(f"Folder not found: {folder_path}")

    files_to_zip: list[str] = []
    seen_dirs: set[tuple[int, int]] = set()

    for root, dirs, files in os.walk(folder_path, followlinks=False):
        try:
            st = os.stat(root)
            key = (st.st_dev, st.st_ino)
            if key in seen_dirs:
                dirs[:] = []
                continue
            seen_dirs.add(key)
        except OSError:
            continue

        dirs[:] = [d for d in dirs if d not in EXCLUDE_DIRS and not d.startswith(".")]
        for f in files:
            if f in EXCLUDE_FILES or f.startswith("."):
                continue
            files_to_zip.append(os.path.join(root, f))

    total = len(files_to_zip)
    os.makedirs(os.path.dirname(zip_path) or ".", exist_ok=True)

    with zipfile.ZipFile(zip_path, "w") as zf:
        if total == 0:
            if callback: callback(1.0)
        else:
            for i, path in enumerate(files_to_zip):
                try:
                    arcname = os.path.relpath(path, folder_path).replace(os.sep, "/")
                    ext = os.path.splitext(path)[1].lower()
                    if ext in INCOMPRESSIBLE_EXTS:
                        zf.write(path, arcname, compress_type=zipfile.ZIP_STORED)
                    else:
                        zf.write(path, arcname, compress_type=zipfile.ZIP_DEFLATED,
                                 compresslevel=9)
                except Exception as e:
                    print(f"Skipping {path}: {e}")
                    continue
                if callback:
                    callback((i + 1) / total)

    hasher = hashlib.sha3_512()
    with open(zip_path, "rb") as f:
        while True:
            chunk = f.read(CHUNK_SIZE)
            if not chunk:
                break
            hasher.update(chunk)
    return hasher.digest()


def validate_zip(zip_path: str) -> None:
    with zipfile.ZipFile(zip_path, "r") as zf:
        bad = zf.testzip()
        if bad is not None:
            raise RuntimeError(f"Corrupt entry in temp ZIP: {bad}")


def verify_rwmod(path: str, expected_min_size: int = 0) -> bool:
    try:
        size = os.path.getsize(path)
        if size < max(1024, expected_min_size):
            return False
        with open(path, "rb") as f:
            head = f.read(16)
        return head.startswith(SIG_LFH) or head.startswith(SIG_RWMOD)
    except OSError:
        return False


def tamper_zip_with_obfuscation(zip_path: str,
                                rwmod_path: str,
                                content_hash_seed: bytes,
                                callback: Optional[Callable[[str, float], None]] = None,
                                n_fakes: int = N_FAKE_EOCD) -> None:
    if not os.path.exists(zip_path):
        raise FileNotFoundError(f"ZIP file not found: {zip_path}")
    os.makedirs(os.path.dirname(rwmod_path) or ".", exist_ok=True)

    zip_size = os.path.getsize(zip_path)
    rng = random.Random(int.from_bytes(content_hash_seed, "big"))

    with tempfile.NamedTemporaryFile(suffix=".zip", delete=False) as tmp:
        shell_path = tmp.name
    try:
        with zipfile.ZipFile(shell_path, "w") as zf:
            zf.writestr("git_mogged.junk", b"")
        with open(shell_path, "rb") as f:
            empty_shell = f.read()
    finally:
        try:
            os.remove(shell_path)
        except OSError:
            pass

    eff_min = min(MIN_JUNK_SIZE, max(512, zip_size // 4))
    eff_max = min(MAX_JUNK_SIZE, max(1024, zip_size // 2))
    if eff_max < eff_min:
        eff_min, eff_max = eff_max, eff_min
    junk_pre  = rng.randint(eff_min, eff_max)
    junk_post = rng.randint(eff_min, eff_max)

    header_seed = hashlib.sha3_256(f"{content_hash_seed}-header".encode()).digest()
    sig_seed    = hashlib.sha3_256(f"{content_hash_seed}-sig".encode()).digest()
    footer_seed = hashlib.sha3_256(f"{content_hash_seed}-footer".encode()).digest()

    real_header = encrypt_with_chaff(get_header_sig(content_hash_seed), header_seed)
    real_sig    = encrypt_with_chaff(mutable_signature(b"real_sig", content_hash_seed), sig_seed)
    nonce       = os.urandom(8)
    rwmod_block = (
        SIG_RWMOD + nonce
        + pack_chunk(SIG_HDR, real_header)
        + pack_chunk(SIG_SIG, real_sig)
    )

    layers = create_obfuscation_layers(content_hash_seed)
    if callback:
        callback("layers", 1.0)

    real_footer  = encrypt_with_chaff(get_footer_sig(content_hash_seed), footer_seed)
    footer_block = pack_chunk(SIG_FTR, real_footer)

    block_start_offset = (
        len(empty_shell) + junk_pre + len(layers) + len(rwmod_block)
        + zip_size + junk_post + len(footer_block)
    )

    fake_block = build_fake_eocd_block(n_fakes, rng, block_start_offset)
    if callback:
        callback("fake_eocd", 1.0)

    est_total = block_start_offset + len(fake_block)
    needed = est_total + 5 * 1024 * 1024
    free = shutil.disk_usage(os.path.dirname(rwmod_path) or ".").free
    if free < needed:
        raise RuntimeError(
            f"Not enough disk space: need ~{needed // 1_000_000} MB, "
            f"have {free // 1_000_000} MB"
        )

    tmp_out = rwmod_path + TEMP_SUFFIX
    try:
        with open(tmp_out, "wb") as out:
            out.write(empty_shell)
            write_random(out, junk_pre)
            out.write(layers)
            out.write(rwmod_block)

            if zip_size >= MMAP_THRESHOLD:
                with open(zip_path, "rb") as src, \
                     mmap.mmap(src.fileno(), 0, access=mmap.ACCESS_READ) as mm:
                    out.write(mm)
                if callback:
                    callback("copy", 1.0)
            else:
                copied = 0
                with open(zip_path, "rb") as src:
                    while True:
                        chunk = src.read(CHUNK_SIZE)
                        if not chunk:
                            break
                        out.write(chunk)
                        copied += len(chunk)
                        if callback and zip_size > 0:
                            callback("copy", copied / zip_size)

            write_random(out, junk_post)
            out.write(footer_block)
            out.write(fake_block)

            out.flush()
            os.fsync(out.fileno())

        if not verify_rwmod(tmp_out, expected_min_size=len(empty_shell) + 1024):
            raise RuntimeError("Output verification failed (truncated or malformed)")

        os.replace(tmp_out, rwmod_path)

        if callback:
            callback("finalize", 1.0)

    except BaseException:
        try:
            os.remove(tmp_out)
        except OSError:
            pass
        raise


def pack_as_rwmod(folder_path: str,
                  rwmod_path: str,
                  callback: Optional[Callable[[str, float], None]] = None,
                  n_fakes: int = N_FAKE_EOCD) -> dict:
    temp_zip = None
    try:
        fd, temp_zip = tempfile.mkstemp(suffix=".zip")
        os.close(fd)

        if callback:
            callback("zip", 0.0)
        t0 = time.perf_counter()
        seed = zip_folder(
            folder_path, temp_zip,
            callback=(lambda p: callback("zip", p * 0.9)) if callback else None,
        )
        t1 = time.perf_counter()

        validate_zip(temp_zip)
        if callback:
            callback("zip", 1.0)

        tamper_zip_with_obfuscation(
            temp_zip, rwmod_path, seed,
            callback=callback, n_fakes=n_fakes,
        )
        t2 = time.perf_counter()

        return {
            "zip_seconds":       round(t1 - t0, 3),
            "obfuscate_seconds": round(t2 - t1, 3),
        }
    finally:
        if temp_zip and os.path.exists(temp_zip):
            try:
                os.remove(temp_zip)
            except OSError:
                pass


# ===========================================================================
# GUI
# ===========================================================================
class RepackerApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        root.title("RWMod Repacker")
        root.geometry("820x740")
        root.minsize(720, 660)

        main = ttk.Frame(root, padding=12)
        main.pack(fill="both", expand=True)

        ttk.Label(main, text="RWMod Repacker",
                  font=("Segoe UI", 16, "bold")).pack(anchor="w", pady=(0, 10))

        # --- SOURCE (folder OR file) ---
        sf = ttk.LabelFrame(main, text="Source - Folder to pack, or .rwmod to validate", padding=8)
        sf.pack(fill="x", pady=4)

        self.source_var = tk.StringVar()
        row = ttk.Frame(sf)
        row.pack(fill="x")
        ttk.Entry(row, textvariable=self.source_var).pack(
            side="left", fill="x", expand=True, padx=(0, 6))
        ttk.Button(row, text="Folder", width=10,
                   command=self.browse_folder).pack(side="left", padx=(0, 4))
        ttk.Button(row, text="File", width=8,
                   command=self.browse_file).pack(side="left")

        # --- OUTPUT (only for Repack) ---
        of = ttk.LabelFrame(main, text="Output Folder (for Repack only)", padding=8)
        of.pack(fill="x", pady=4)
        self.output_var = tk.StringVar()
        ttk.Entry(of, textvariable=self.output_var).pack(
            side="left", fill="x", expand=True, padx=(0, 6))
        ttk.Button(of, text="Browse...", command=self.browse_output).pack(side="right")

        # --- Progress ---
        pf = ttk.LabelFrame(main, text="Progress", padding=8)
        pf.pack(fill="x", pady=4)
        self.progress = ttk.Progressbar(pf, mode="determinate", maximum=100)
        self.progress.pack(fill="x", pady=(0, 4))
        self.status_var = tk.StringVar(value="Ready.")
        ttk.Label(pf, textvariable=self.status_var).pack(anchor="w")

        # --- Log ---
        lf = ttk.LabelFrame(main, text="Activity Log", padding=8)
        lf.pack(fill="both", expand=True, pady=4)
        self.log = scrolledtext.ScrolledText(lf, wrap="word", height=13,
                                             state="disabled",
                                             font=("Consolas", 9))
        self.log.pack(fill="both", expand=True)

        # --- Action buttons ---
        bf = ttk.Frame(main)
        bf.pack(fill="x", pady=(8, 0))
        self.validate_btn = ttk.Button(bf, text="Validate .rwmod",
                                       command=self.start_validate)
        self.validate_btn.pack(side="left")
        self.repack_btn = ttk.Button(bf, text="REPACK AS .RWMOD",
                                     command=self.start_repack)
        self.repack_btn.pack(side="right")

        self._last_log = {}
        self.append_log("RWMod Repacker ready.")
        self.append_log("- Point Source at a FOLDER to Repack")
        self.append_log("- Point Source at a .rwmod FILE to Validate")

    # ---- UI helpers ----
    def append_log(self, msg: str) -> None:
        self.log.configure(state="normal")
        self.log.insert("end", msg + "\n")
        self.log.see("end")
        self.log.configure(state="disabled")

    def log_from_thread(self, msg: str) -> None:
        self.root.after(0, lambda m=msg: self.append_log(m))

    def set_status(self, text: str) -> None:
        self.root.after(0, lambda: self.status_var.set(text))

    def set_progress(self, value: float) -> None:
        self.root.after(0, lambda: self.progress.configure(value=value))

    # ---- Browse ----
    def browse_folder(self) -> None:
        p = filedialog.askdirectory(title="Select MOD Folder")
        if p:
            self.source_var.set(p)
            self.append_log(f"Folder: {p}")

    def browse_file(self) -> None:
        p = filedialog.askopenfilename(
            title="Select .rwmod file",
            filetypes=[("RWMod", "*.rwmod"), ("ZIP", "*.zip"), ("All", "*.*")])
        if p:
            self.source_var.set(p)
            self.append_log(f"File: {p}")

    def browse_output(self) -> None:
        p = filedialog.askdirectory(title="Select Output Folder")
        if p:
            self.output_var.set(p)
            self.append_log(f"Output folder: {p}")

    # ---- Validate ----
    def start_validate(self) -> None:
        src = self.source_var.get().strip()
        if not src or not os.path.isfile(src):
            messagebox.showerror(
                "Error",
                "Validate needs a .rwmod FILE.\n\n"
                "Click 'File' to pick one."
            )
            return

        self.validate_btn.configure(state="disabled")
        self.set_status("Validating...")
        self.append_log("")
        self.append_log("=" * 60)
        self.append_log(f"VALIDATING: {src}")
        self.append_log("=" * 60)

        def worker():
            try:
                report, is_valid = validate_rwmod_report(src)
                for line in report.splitlines():
                    self.log_from_thread(line)
                self.set_status("Valid" if is_valid else "Invalid")
                self.root.after(0, lambda: messagebox.showinfo(
                    "Validation Result",
                    "File is VALID and should load in RW."
                    if is_valid else
                    "File is INVALID and will NOT load in RW."
                ))
            except Exception as e:
                self.log_from_thread(f"Validation error: {e}")
                self.set_status("Validation failed.")
            finally:
                self.root.after(0, lambda: self.validate_btn.configure(state="normal"))

        threading.Thread(target=worker, daemon=True).start()

    # ---- Repack ----
    def start_repack(self) -> None:
        folder = self.source_var.get().strip()
        output = self.output_var.get().strip()

        if not folder or not os.path.isdir(folder):
            messagebox.showerror(
                "Error",
                "Repack needs a FOLDER.\n\n"
                "Click 'Folder' to pick one."
            )
            return
        if not output or not os.path.isdir(output):
            messagebox.showerror("Error", "Please select a valid output folder.")
            return

        self.set_status("Scanning folder...")
        self.append_log("")
        self.append_log("-" * 60)
        self.append_log("Pre-flight validation...")

        rpt = scan_folder(folder)
        self.append_log(rpt.summary())

        if rpt.total_files == 0:
            messagebox.showerror("Empty Folder",
                                 "The selected folder has no files to pack.")
            self.set_status("Aborted - empty folder.")
            return

        if not rpt.has_mod_info:
            go = messagebox.askyesno(
                "Missing mod-info.txt",
                "No mod-info.txt found at the top level of this folder.\n\n"
                "Rusted Warfare may reject mods without it.\n\n"
                "Pack anyway?"
            )
            if not go:
                self.append_log("User cancelled - missing mod-info.txt.")
                self.set_status("Aborted by user.")
                return

        modname = os.path.basename(folder.rstrip("/\\")) or "mod"
        rwmod_path = os.path.join(output, modname + ".rwmod")
        if os.path.exists(rwmod_path):
            go = messagebox.askyesno(
                "File exists",
                f"Output already exists:\n{rwmod_path}\n\nOverwrite?"
            )
            if not go:
                self.append_log("User cancelled - output exists.")
                self.set_status("Aborted by user.")
                return

        confirm = messagebox.askyesno(
            "Confirm Repack",
            f"Ready to pack.\n\n"
            f"Source:      {folder}\n"
            f"Output:      {rwmod_path}\n"
            f"Files:       {rpt.total_files:,}\n"
            f"Size:        {rpt.total_bytes / 1_048_576:.2f} MB\n"
            f"Fake EOCDs:  {N_FAKE_EOCD}\n\n"
            f"Proceed?"
        )
        if not confirm:
            self.append_log("User cancelled at confirmation dialog.")
            self.set_status("Aborted by user.")
            return

        self.repack_btn.configure(state="disabled")
        self.progress.configure(value=0)
        self.set_status("Starting...")
        self.append_log("Starting repack...")

        threading.Thread(target=self._run_repack,
                         args=(folder, rwmod_path), daemon=True).start()

    def _run_repack(self, folder: str, rwmod_path: str) -> None:
        try:
            self.log_from_thread(f"Source: {folder}")
            self.log_from_thread(f"Target: {rwmod_path}")

            def cb(stage: str, fraction: float) -> None:
                start, end = STAGE_WEIGHTS.get(stage, (0, 100))
                overall = start + fraction * (end - start)
                self.set_progress(overall)

                label = {
                    "zip":       "Archiving MOD folder",
                    "layers":    "Building obfuscation layers",
                    "copy":      "Embedding ZIP payload",
                    "fake_eocd": "Injecting fake EOCD data",
                    "finalize":  "Finalizing",
                }.get(stage, stage)
                self.set_status(f"{label}... {int(fraction * 100)}%")

                bucket = int(fraction * 5)
                if self._last_log.get(stage) != bucket:
                    self._last_log[stage] = bucket
                    self.log_from_thread(f"{label}... {int(fraction * 100)}%")

            timings = pack_as_rwmod(
                folder, rwmod_path, callback=cb, n_fakes=N_FAKE_EOCD)

            out_size = os.path.getsize(rwmod_path)
            self.log_from_thread("")
            self.log_from_thread("Repack complete!")
            self.log_from_thread(f"Output: {rwmod_path}")
            self.log_from_thread(f"Size:   {out_size / 1_048_576:.2f} MB")
            self.log_from_thread(f"ZIP:        {timings['zip_seconds']}s")
            self.log_from_thread(f"Obfuscate: {timings['obfuscate_seconds']}s")
            self.set_progress(100)
            self.set_status("Done.")

            self.root.after(0, lambda: messagebox.showinfo(
                "Success",
                f"Successfully created:\n{rwmod_path}\n\n"
                f"Fake EOCDs: {N_FAKE_EOCD}"
            ))

        except Exception as e:
            self.log_from_thread(f"Error: {e}")
            self.set_status("Failed.")
            self.root.after(0, lambda err=e: messagebox.showerror(
                "Error", f"Repack failed:\n\n{err}"))
        finally:
            self.root.after(0, lambda: self.repack_btn.configure(state="normal"))


# ===========================================================================
# ENTRY
# ===========================================================================
def main() -> None:
    root = tk.Tk()
    try:
        ttk.Style(root).theme_use("clam")
    except Exception:
        pass
    RepackerApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()