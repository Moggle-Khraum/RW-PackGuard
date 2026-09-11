"""
RWMod Repacker - Obfuscation & Protection Tool

SECURITY MODEL:
  - This tool uses OBFUSCATION, NOT ENCRYPTION
  - Obfuscation hides mods from casual extraction (7-Zip, WinRAR, etc.)
  - Rusted Warfare can still load protected mods (has native support)
  - A determined attacker with ZIP knowledge can extract the real archive
  - NO PASSWORD PROTECTION - RW must be able to read the content
  - Think of it as "security by obscurity" for mod distribution

GUI:
  Source field   -> can be a FOLDER (for Repack) or an .rwmod FILE (for Validate)
  Browse buttons -> Folder or File - both write to Source
  Repack         -> packs a folder into .rwmod with obfuscation layers
  Validate       -> checks an .rwmod file (clean or protected)
"""

from __future__ import annotations

import hashlib
import hmac
import io
import logging
import mmap
import os
import secrets
import shutil
import string
import struct
import tempfile
import threading
import time
import zipfile
from pathlib import Path
from queue import Queue
from typing import Callable, Optional, Union, TypedDict

import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext


# ===========================================================================
# LOGGING SETUP
# ===========================================================================
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s [%(levelname)s] %(name)s: %(message)s'
)
logger = logging.getLogger("RWModGuard")


# ===========================================================================
# CONFIG & LIMITS
# ===========================================================================
LAYERS        = 13
MIN_JUNK_SIZE = 11_392
MAX_JUNK_SIZE = 11_584

# **FILE SIZE LIMITS**
MAX_FILE_SIZE = 2 * 1024**3  # 2 GB - prevents OOM
MAX_VALIDATION_SIZE = 500 * 1024**2  # 500 MB for streaming validation

EOCD_SIG        = b"PK\x05\x06"
CD_SIG          = b"PK\x01\x02"
EOCD_SIZE       = 22
N_FAKE_EOCD     = 100
FAKE_TRAIL_JUNK = (4_096, 12_288)

# **SCRAMBLED SIGNATURE GENERATION** (not fixed magic bytes)
# These are now generated at runtime instead of hardcoded
def _gen_sig() -> bytes:
    """Generate pseudo-random signature that changes each run."""
    return secrets.token_bytes(4)

SIG_LFH   = b"PK\x03\x04"  # Keep ZIP magic, can't change
SIG_RWMOD = b"RWMOD"       # Real archive marker

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
# TYPE DEFINITIONS
# ===========================================================================
class PackResult(TypedDict):
    """Result of packing operation."""
    zip_seconds: float
    obfuscate_seconds: float
    input_size: int
    output_size: int
    protected: bool


class EOCDInfo(TypedDict):
    """Parsed EOCD record information."""
    pos: int
    disk_num: int
    cd_start_dk: int
    entries_dk: int
    entries_all: int
    cd_size: int
    cd_offset: int
    comment_len: int


# ===========================================================================
# HELPERS
# ===========================================================================
def pack_chunk(tag: bytes, payload: bytes) -> bytes:
    """Pack data with TLV format: tag + length + payload."""
    return tag + len(payload).to_bytes(4, "big") + payload


def write_random(out, n: int) -> None:
    """Write n random bytes to file, using pre-buffered entropy."""
    while n > 0:
        take = min(n, RANDOM_BUF_SIZE)
        out.write(_RANDOM_BUF[:take])
        n -= take


def u16(b, o): 
    """Unpack unsigned 16-bit little-endian integer."""
    return struct.unpack_from("<H", b, o)[0]

def u32(b, o): 
    """Unpack unsigned 32-bit little-endian integer."""
    return struct.unpack_from("<I", b, o)[0]


def validate_file_path(path: str, must_exist: bool = True, max_size: int = MAX_FILE_SIZE) -> None:
    """
    Validate file path for safety.
    
    Args:
        path: File path to validate
        must_exist: If True, file must exist
        max_size: Maximum file size in bytes
        
    Raises:
        ValueError: If validation fails
    """
    if not path or not isinstance(path, str):
        raise ValueError("Invalid path: must be non-empty string")
    
    if must_exist and not os.path.exists(path):
        raise ValueError(f"File not found: {path}")
    
    if must_exist and os.path.isfile(path):
        size = os.path.getsize(path)
        if size > max_size:
            raise ValueError(
                f"File too large: {size / 1024**2:.1f} MB "
                f"(max {max_size / 1024**2:.1f} MB)"
            )


def find_all_eocds(data: bytes) -> list[int]:
    """Find all EOCD (End of Central Directory) signatures in data."""
    out = []
    i = 0
    while True:
        j = data.find(EOCD_SIG, i)
        if j < 0:
            break
        out.append(j)
        i = j + 1
    return out


def parse_eocd(data: bytes, pos: int) -> Optional[EOCDInfo]:
    """
    Parse EOCD record at given position.
    
    Args:
        data: Bytes to parse
        pos: Position of EOCD signature
        
    Returns:
        Dict with EOCD fields, or None if invalid
    """
    if pos + EOCD_SIZE > len(data):
        return None
    try:
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
    except struct.error as e:
        logger.debug(f"Failed to parse EOCD at {pos}: {e}")
        return None


def try_eocd(data: bytes, eocd_pos: int, e: EOCDInfo) -> tuple[bool, Union[list[str], str]]:
    """
    Try to validate EOCD and extract file list.
    
    Returns:
        (is_valid, file_list_or_error_msg)
    """
    if e["comment_len"] > 65535:
        return False, "comment length exceeds 65535"
    
    cd_size = e["cd_size"]
    cd_offset = e["cd_offset"]
    
    if cd_size > eocd_pos:
        return False, "CD size exceeds archive start"
    
    archive_start = eocd_pos - cd_size - cd_offset
    if archive_start < 0:
        return False, "archive start would be negative"
    
    cd_in_file = archive_start + cd_offset
    if cd_in_file + 4 > len(data):
        return False, "CD position past EOF"
    if data[cd_in_file:cd_in_file + 4] != CD_SIG:
        return False, "no PK\\x01\\x02 at computed CD position"
    
    eocd_end = eocd_pos + EOCD_SIZE + e["comment_len"]
    if eocd_end > len(data):
        return False, "EOCD end past EOF"
    
    try:
        blob = data[archive_start:eocd_end]
        with zipfile.ZipFile(io.BytesIO(blob)) as zf:
            names = zf.namelist()
            return True, names
    except Exception as e:
        return False, f"{type(e).__name__}: {str(e)[:60]}"


# ===========================================================================
# VALIDATION (Streaming for large files)
# ===========================================================================
def validate_rwmod_report(path: str) -> tuple[str, bool]:
    """
    Validate .rwmod file and return detailed report.
    
    Uses streaming for files > MAX_VALIDATION_SIZE to avoid OOM.
    """
    try:
        validate_file_path(path, must_exist=True, max_size=MAX_FILE_SIZE)
    except ValueError as e:
        return f"INVALID - {e}", False
    
    file_size = os.path.getsize(path)
    lines = []
    lines.append(f"File:    {path}")
    lines.append(f"Size:    {file_size:,} bytes ({file_size / 1_048_576:.2f} MB)")
    lines.append("")
    
    try:
        # For large files, only read tail to find EOCD
        if file_size > MAX_VALIDATION_SIZE:
            logger.info(f"File {file_size / 1024**2:.1f} MB - using streaming validation")
            with open(path, "rb") as f:
                f.seek(max(0, file_size - 64 * 1024))
                data = f.read()
        else:
            with open(path, "rb") as f:
                data = f.read()
    except OSError as e:
        lines.append(f"ERROR: Failed to read file: {e}")
        return "\n".join(lines), False
    
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
        lines.append(f"🔒 PROTECTED - {fakes_skipped} fake EOCD(s) detected.")
        lines.append("   External tools (7-Zip, WinRAR, etc.) will fail.")
        lines.append("   Rusted Warfare should still load this file.")
    else:
        lines.append("⚪ CLEAN - no fake EOCDs detected.")
    
    lines.append("")
    lines.append("First entries in archive:")
    for n in names[:12]:
        lines.append(f"   - {n}")
    if len(names) > 12:
        lines.append(f"   ... and {len(names) - 12} more")
    
    return "\n".join(lines), True


# ===========================================================================
# OBFUSCATION (Using secrets, not random)
# ===========================================================================
def get_header_sig(file_data: Optional[bytes] = None) -> bytes:
    """
    Generate obfuscated header signature using cryptographically secure random.
    
    Args:
        file_data: Optional data to derive deterministic seed from
        
    Returns:
        Scrambled header bytes
    """
    if file_data:
        seed = hashlib.sha3_512(file_data).digest()[:16]
        rng_source = lambda n: hashlib.shake_256(seed).digest(n)
    else:
        rng_source = lambda n: secrets.token_bytes(n)
    
    patterns = [
        lambda: bytes([secrets.randbelow(256), 0x50 + secrets.randbelow(15),
                       0x4E + secrets.choice([0, 1, -1]) % 256, secrets.choice([0x47, 0x46, 0x48]),
                       0x0D, 0x0A, secrets.choice([0x1A, 0x1B, 0x1C]),
                       secrets.choice([0x00, 0x0A, 0xFF])]),
        lambda: bytes([0x50, 0x4B, secrets.choice([0x03, 0x05, 0x07]), 0x04,
                       secrets.randbelow(16) + 0x10, 0x00, 0x00,
                       secrets.choice([0x08, 0x00])]),
        lambda: bytes([secrets.randbelow(240) + 0x10, secrets.randbelow(96) + 0x20,
                       secrets.randbelow(32), secrets.randbelow(64) + 0xC0,
                       secrets.choice([0x00, 0xFF]), secrets.randbelow(224) + 0x10]),
    ]
    
    header = bytearray(secrets.choice(patterns)())
    
    def mutate_byte(b: int) -> int:
        """Apply random mutations to byte."""
        b ^= 0xFF
        b = (b + secrets.randbelow(255) + 1) % 256
        b = (b - secrets.randbelow(255) - 1) % 256
        return secrets.randbelow(256)
    
    for _ in range(5):
        pos = secrets.randbelow(len(header))
        header[pos] = mutate_byte(header[pos])
    
    trailer_len = secrets.randbelow(7) + 2
    trailer = bytearray([secrets.randbelow(256) for _ in range(trailer_len)])
    for i in range(len(trailer)):
        for _ in range(5):
            trailer[i] = mutate_byte(trailer[i])
    
    if secrets.randbelow(10) > 7:
        insert_pos = secrets.randbelow(len(header) - 1) + 1
        header = header[:insert_pos] + trailer + header[insert_pos:]
    else:
        header += trailer
    
    return bytes(header)


def get_footer_sig(file_data: Optional[bytes] = None) -> bytes:
    """Generate obfuscated footer signature."""
    patterns = [
        lambda: (
            "".join(secrets.choice(string.ascii_letters + string.digits) for _ in range(secrets.randbelow(9) + 8)).encode("ascii")
            + secrets.choice([b"--", b"~~", b"||", b"::", b"$$"])
            + bytes([secrets.randbelow(95) + 32 for _ in range(secrets.randbelow(9) + 8)])
            + secrets.choice([b"\x00\x00", b"\xFF\xFF", b"\xFE\xFE", b"\x01\x01"])
        ),
        lambda: (
            bytes([secrets.randbelow(128) + 0x80 for _ in range(secrets.randbelow(7) + 6)])
            + bytes([secrets.randbelow(128) for _ in range(secrets.randbelow(5) + 4)])
            + secrets.choice([b"\x55\xAA", b"\xAA\x55", b"\xC3\x3C"])
        ),
    ]
    
    footer = bytearray(secrets.choice(patterns)())
    mutations = ["xor", "swap", "rotate", "multiply_mod", "divide_mod", "insert"]
    secrets.SystemRandom().shuffle(mutations)
    
    for mutation in mutations:
        if mutation == "xor":
            for pos in range(len(footer)):
                footer[pos] ^= 0xFF
        elif mutation == "swap":
            for pos in range(len(footer) - 1):
                footer[pos], footer[pos + 1] = footer[pos + 1], footer[pos]
        elif mutation == "rotate":
            for pos in range(len(footer)):
                shift = secrets.randbelow(7) + 1
                footer[pos] = ((footer[pos] << shift) | (footer[pos] >> (8 - shift))) & 0xFF
        elif mutation == "multiply_mod":
            mul = secrets.randbelow(14) + 2
            for pos in range(len(footer)):
                footer[pos] = (footer[pos] * mul) % 256
        elif mutation == "divide_mod":
            div = secrets.randbelow(14) + 2
            for pos in range(len(footer)):
                footer[pos] = (footer[pos] // div) % 256
        elif mutation == "insert":
            new_footer = bytearray()
            for pos in range(len(footer)):
                new_footer.append(footer[pos])
                if len(new_footer) < 100 and secrets.randbelow(5) == 0:
                    new_footer.append(secrets.randbelow(256))
            footer = new_footer
    
    return bytes(footer)


def mutable_signature(base: Union[bytes, str], seed: Optional[bytes] = None,
                      heavy: bool = True) -> bytes:
    """
    Create mutable obfuscated signature using cryptographically secure random.
    
    Args:
        base: Base data to obfuscate
        seed: Seed for deterministic generation
        heavy: If True, apply more mutations
        
    Returns:
        Obfuscated bytes
    """
    base_bytes = base.encode("utf-8") if isinstance(base, str) else base
    base_hash = hashlib.sha256(base_bytes).digest()
    noise_len = (base_hash[0] % 32) + 16
    
    np = secrets.randbelow(4)
    if np == 0:
        noise = bytes([secrets.randbelow(256) for _ in range(noise_len)])
    elif np == 1:
        chars = string.ascii_letters + string.digits + string.punctuation
        noise = "".join(secrets.choice(chars) for _ in range(noise_len)).encode("ascii")
    elif np == 2:
        start = secrets.randbelow(256)
        step = secrets.choice([1, -1, 2, -2, 5])
        noise = bytes([(start + i * step) % 256 for i in range(noise_len)])
    else:
        key = secrets.randbelow(255) + 1
        base_val = secrets.randbelow(256)
        noise = bytes([(base_val + i) % 256 ^ key for i in range(noise_len)])
    
    ip = secrets.randbelow(len(base_bytes) + 1)
    if secrets.randbelow(2) == 0:
        sig = bytearray(base_bytes[:ip] + noise + base_bytes[ip:])
    else:
        nb = noise[:secrets.randbelow(len(noise) + 1)]
        na = noise[len(nb):]
        sig = bytearray(nb + base_bytes + na)
    
    passes = secrets.randbelow(8) + 8 if heavy else secrets.randbelow(4) + 3
    for _ in range(passes):
        t = secrets.randbelow(10)
        pos = secrets.randbelow(len(sig))
        
        if t == 0:
            sig[pos] ^= secrets.randbelow(255) + 1
        elif t == 1:
            if len(sig) > 4:
                s = secrets.randbelow(len(sig) - 2)
                e = min(len(sig), s + secrets.randbelow(7) + 2)
                ch = sig[s:e]; ch.reverse(); sig[s:e] = ch
        elif t == 2:
            sh = secrets.randbelow(7) + 1
            sig[pos] = ((sig[pos] << sh) | (sig[pos] >> (8 - sh))) & 0xFF
        elif t == 3:
            sh = secrets.randbelow(7) + 1
            sig[pos] = ((sig[pos] >> sh) | (sig[pos] << (8 - sh))) & 0xFF
        elif t == 4:
            if len(sig) < 256:
                sig.insert(pos, secrets.randbelow(256))
        elif t == 5:
            if len(sig) > 8:
                del sig[pos]
        elif t == 6:
            f = secrets.randbelow(14) + 2
            sig[pos] = (sig[pos] * f) % 256
        elif t == 7:
            d = secrets.randbelow(15) + 1
            sig[pos] = (sig[pos] // d) % 256
        elif t == 8:
            if len(sig) > 12:
                sz = secrets.randbelow(4) + 3
                i = secrets.randbelow(max(1, len(sig) - sz))
                j = secrets.randbelow(max(1, len(sig) - sz))
                if i != j:
                    a = sig[i:i + sz]; b = sig[j:j + sz]
                    sig[i:i + sz], sig[j:j + sz] = b, a
        else:
            fr = hashlib.md5(sig).digest()
            sig[pos] = fr[secrets.randbelow(len(fr))]
    
    if heavy and len(sig) > 32:
        sig_list = list(sig)
        secrets.SystemRandom().shuffle(sig_list)
        sig = bytearray(sig_list)
    
    return bytes(sig)


def polymorphic_encoder(data: bytes, seed: bytes) -> bytes:
    """
    Multi-stage encoding using seed-derived parameters.
    
    Args:
        data: Data to encode
        seed: Seed for deterministic encoding
        
    Returns:
        Encoded bytes
    """
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
            rng = secrets.SystemRandom()
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
    Derive ephemeral key mixing seed with unreproducible entropy.
    
    Unlike seed-only derivation, this can never be reconstructed
    since it includes PID, nanosecond timestamp, and os.urandom().
    """
    entropy = f"{os.getpid()}-{time.time_ns()}-{secrets.token_hex(16)}".encode()
    d1 = hashlib.sha3_512(seed + entropy).digest()
    d2 = hashlib.blake2b(d1, digest_size=32).digest()
    d3 = hashlib.shake_256(d2).digest(32)
    
    key = bytearray(d3)
    mask = secrets.randbelow(255) + 1
    xor_k = d2[secrets.randbelow(len(d2))]
    for i in range(len(key)):
        key[i] ^= mask
        key[i] ^= xor_k
        key[i] = ((key[i] << 1) | (key[i] >> 7)) & 0xFF
    
    key_list = list(key)
    secrets.SystemRandom().shuffle(key_list)
    key = bytearray(key_list)
    
    tag = hmac.new(d1, key, hashlib.sha3_256).digest()[:8]
    return bytes(key) + tag


def encrypt_with_chaff(real_data: bytes, seed: bytes) -> bytes:
    """Encrypt data with embedded chaff (decoys) to obscure content."""
    data = bytearray(real_data)
    
    for _ in range(secrets.randbelow(21) + 10):
        pos = secrets.randbelow(len(data) + 1)
        cl = secrets.randbelow(15) + 2
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
    """
    Create 13 layers of obfuscation with varying structures.
    
    Args:
        content_hash_seed: Hash of original ZIP content
        
    Returns:
        Obfuscation layer data
    """
    # Generate dynamic signatures instead of using fixed ones
    SIG_LAYER = _gen_sig()
    SIG_RWF = _gen_sig()
    SIG_LOCK = _gen_sig()
    
    layers = bytearray()
    mode_key = b"OBFUSCATION_KEY"
    
    for i in range(LAYERS):
        layer_seed = hashlib.sha3_256(f"{content_hash_seed}-layer-{i}".encode()).digest()
        
        fake_header = SIG_LFH + os.urandom(secrets.randbelow(193) + 64)
        misaligned = os.urandom(secrets.randbelow(385) + 128)
        layers.extend(pack_chunk(SIG_LAYER, fake_header + misaligned))
        
        for _ in range(secrets.randbelow(4) + 3):
            fake_rwmod = SIG_RWMOD + os.urandom(secrets.randbelow(81) + 60)
            sig = mutable_signature(mode_key, layer_seed)
            layers.extend(pack_chunk(SIG_RWF, fake_rwmod + sig))
        
        trap = polymorphic_encoder(os.urandom(256), layer_seed)
        layers.extend(pack_chunk(SIG_LOCK, trap))
    
    final_hash = hashlib.sha512(layers).digest()
    return bytes(layers) + final_hash


def build_fake_eocd_block(n_fakes: int, rng_seed: bytes) -> bytes:
    """Build block of n_fakes EOCD records to confuse extractors."""
    block = bytearray()
    
    for i in range(n_fakes):
        seed = hashlib.sha3_256(f"{rng_seed}-fake-{i}".encode()).digest()
        
        entries = secrets.randbelow(1000)
        cd_size = secrets.randbelow(50000) + 1000
        cd_offset = secrets.randbelow(1000000)
        
        eocd = EOCD_SIG
        eocd += bytes([0, 0])  # disk number
        eocd += bytes([0, 0])  # disk with CD start
        eocd += entries.to_bytes(2, "little")
        eocd += entries.to_bytes(2, "little")
        eocd += cd_size.to_bytes(4, "little")
        eocd += cd_offset.to_bytes(4, "little")
        eocd += bytes([0, 0])  # comment length
        
        block.extend(eocd)
        block.extend(os.urandom(secrets.randbelow(256)))
    
    return bytes(block)


# ===========================================================================
# FOLDER SCAN
# ===========================================================================
class FolderReport:
    """Report from scanning a folder."""
    
    def __init__(self):
        self.total_files: int = 0
        self.total_bytes: int = 0
        self.has_mod_info: bool = False
        self.mod_info_size: int = 0
        self.top_level_files: list[str] = []
        self.warnings: list[str] = []
    
    def summary(self) -> str:
        """Generate text summary of folder scan."""
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
    """Scan folder for packing, checking size and mod-info presence."""
    rpt = FolderReport()
    try:
        validate_file_path(folder_path, must_exist=True, max_size=MAX_FILE_SIZE)
    except ValueError as e:
        rpt.warnings.append(str(e))
        return rpt
    
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
        except OSError as e:
            logger.warning(f"Failed to stat {root}: {e}")
            continue
        
        dirs[:] = [d for d in dirs if d not in EXCLUDE_DIRS and not d.startswith(".")]
        
        for f in files:
            if f in EXCLUDE_FILES or f.startswith("."):
                continue
            full = os.path.join(root, f)
            try:
                size = os.path.getsize(full)
            except OSError as e:
                logger.debug(f"Skipping {full}: {e}")
                continue
            rpt.total_files += 1
            rpt.total_bytes += size
            
            if rpt.total_bytes > MAX_FILE_SIZE:
                rpt.warnings.append(
                    f"Total folder size exceeds {MAX_FILE_SIZE / 1024**3:.1f} GB - "
                    f"cannot pack"
                )
                return rpt
            
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
            "mod-info.txt not found at top level. "
            "Rusted Warfare may reject this mod."
        )
    return rpt


# ===========================================================================
# ZIP + PACKING
# ===========================================================================
def zip_folder(folder_path: str, zip_path: str,
               callback: Optional[Callable[[float], None]] = None) -> bytes:
    """
    ZIP folder and return SHA3-512 hash of ZIP.
    
    Args:
        folder_path: Source folder
        zip_path: Output ZIP path
        callback: Progress callback (0.0 to 1.0)
        
    Returns:
        SHA3-512 digest of ZIP
        
    Raises:
        FileNotFoundError: If folder doesn't exist
    """
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
    
    logger.info(f"Zipping {total} files to {zip_path}")
    
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
                    logger.warning(f"Skipping {path}: {e}")
                    continue
                if callback:
                    callback((i + 1) / total)
    
    logger.info(f"ZIP created, computing hash...")
    hasher = hashlib.sha3_512()
    with open(zip_path, "rb") as f:
        while True:
            chunk = f.read(CHUNK_SIZE)
            if not chunk:
                break
            hasher.update(chunk)
    
    digest = hasher.digest()
    logger.info(f"ZIP hash: {digest.hex()[:16]}...")
    return digest


def validate_zip(zip_path: str) -> None:
    """Validate ZIP file integrity."""
    with zipfile.ZipFile(zip_path, "r") as zf:
        bad = zf.testzip()
        if bad is not None:
            raise RuntimeError(f"Corrupt entry in temp ZIP: {bad}")


def verify_rwmod(path: str, expected_min_size: int = 0) -> bool:
    """Verify .rwmod file is readable."""
    try:
        size = os.path.getsize(path)
        if size < max(1024, expected_min_size):
            return False
        with open(path, "rb") as f:
            head = f.read(16)
        return head.startswith(SIG_LFH) or head.startswith(SIG_RWMOD)
    except OSError:
        return False


def cleanup_temp_files(rwmod_path: str) -> None:
    """Clean up any leftover .part files."""
    tmp_out = rwmod_path + TEMP_SUFFIX
    try:
        if os.path.exists(tmp_out):
            os.remove(tmp_out)
            logger.info(f"Cleaned up {tmp_out}")
    except OSError as e:
        logger.warning(f"Failed to clean temp file {tmp_out}: {e}")


def tamper_zip_with_obfuscation(zip_path: str,
                                rwmod_path: str,
                                content_hash_seed: bytes,
                                callback: Optional[Callable[[str, float], None]] = None,
                                n_fakes: int = N_FAKE_EOCD) -> None:
    """
    Wrap ZIP in obfuscation layers and write .rwmod file.
    
    Uses chunked copying to optimize memory for large files.
    """
    if not os.path.exists(zip_path):
        raise FileNotFoundError(f"ZIP file not found: {zip_path}")
    
    zip_size = os.path.getsize(zip_path)
    logger.info(f"Obfuscating {zip_size / 1024**2:.1f} MB ZIP")
    
    os.makedirs(os.path.dirname(rwmod_path) or ".", exist_ok=True)
    
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
    junk_pre  = secrets.randbelow(eff_max - eff_min + 1) + eff_min
    junk_post = secrets.randbelow(eff_max - eff_min + 1) + eff_min
    
    header_seed = hashlib.sha3_256(f"{content_hash_seed}-header".encode()).digest()
    sig_seed    = hashlib.sha3_256(f"{content_hash_seed}-sig".encode()).digest()
    footer_seed = hashlib.sha3_256(f"{content_hash_seed}-footer".encode()).digest()
    
    real_header = encrypt_with_chaff(get_header_sig(content_hash_seed), header_seed)
    real_sig    = encrypt_with_chaff(mutable_signature(b"real_sig", content_hash_seed), sig_seed)
    nonce       = os.urandom(8)
    rwmod_block = (
        SIG_RWMOD + nonce
        + pack_chunk(b"HDR_", real_header)
        + pack_chunk(b"SIG_", real_sig)
    )
    
    layers = create_obfuscation_layers(content_hash_seed)
    if callback:
        callback("layers", 1.0)
    logger.info(f"Created {len(layers) / 1024:.1f} KB obfuscation layers")
    
    real_footer  = encrypt_with_chaff(get_footer_sig(content_hash_seed), footer_seed)
    footer_block = pack_chunk(b"FTR_", real_footer)
    
    block_start_offset = (
        len(empty_shell) + junk_pre + len(layers) + len(rwmod_block)
        + zip_size + junk_post + len(footer_block)
    )
    
    fake_block = build_fake_eocd_block(n_fakes, hashlib.sha3_256(content_hash_seed).digest())
    if callback:
        callback("fake_eocd", 1.0)
    logger.info(f"Created {len(fake_block) / 1024:.1f} KB fake EOCD block")
    
    est_total = block_start_offset + len(fake_block)
    needed = est_total + 5 * 1024 * 1024
    free = shutil.disk_usage(os.path.dirname(rwmod_path) or ".").free
    if free < needed:
        raise RuntimeError(
            f"Not enough disk space: need ~{needed // 1_000_000} MB, "
            f"have {free // 1_000_000} MB"
        )
    
    cleanup_temp_files(rwmod_path)
    tmp_out = rwmod_path + TEMP_SUFFIX
    
    try:
        with open(tmp_out, "wb") as out:
            out.write(empty_shell)
            write_random(out, junk_pre)
            out.write(layers)
            out.write(rwmod_block)
            
            # **CHUNKED COPYING FOR MEMORY EFFICIENCY**
            copied = 0
            if zip_size >= MMAP_THRESHOLD:
                with open(zip_path, "rb") as src, \
                     mmap.mmap(src.fileno(), 0, access=mmap.ACCESS_READ) as mm:
                    for chunk_start in range(0, len(mm), CHUNK_SIZE):
                        chunk_end = min(chunk_start + CHUNK_SIZE, len(mm))
                        out.write(mm[chunk_start:chunk_end])
                        copied = chunk_end
                        if callback:
                            callback("copy", copied / zip_size)
                logger.info("ZIP copied via mmap")
            else:
                with open(zip_path, "rb") as src:
                    while True:
                        chunk = src.read(CHUNK_SIZE)
                        if not chunk:
                            break
                        out.write(chunk)
                        copied += len(chunk)
                        if callback and zip_size > 0:
                            callback("copy", copied / zip_size)
                logger.info("ZIP copied via sequential read")
            
            write_random(out, junk_post)
            out.write(footer_block)
            out.write(fake_block)
            
            out.flush()
            os.fsync(out.fileno())
            logger.info(f"Flushed and synced {tmp_out}")
        
        if not verify_rwmod(tmp_out, expected_min_size=len(empty_shell) + 1024):
            raise RuntimeError("Output verification failed (truncated or malformed)")
        
        os.replace(tmp_out, rwmod_path)
        logger.info(f"Finalized {rwmod_path}")
        
        if callback:
            callback("finalize", 1.0)
    
    except BaseException as e:
        logger.error(f"Packing failed: {e}", exc_info=True)
        cleanup_temp_files(rwmod_path)
        raise


def pack_as_rwmod(folder_path: str,
                  rwmod_path: str,
                  callback: Optional[Callable[[str, float], None]] = None,
                  n_fakes: int = N_FAKE_EOCD) -> PackResult:
    """
    Pack folder as .rwmod with obfuscation.
    
    Returns:
        PackResult with timing and size info
    """
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
        logger.info(f"ZIP validation passed")
        
        input_size = sum(
            os.path.getsize(os.path.join(root, f))
            for root, dirs, files in os.walk(folder_path)
            for f in files if f not in EXCLUDE_FILES
        )
        
        tamper_zip_with_obfuscation(
            temp_zip, rwmod_path, seed,
            callback=callback, n_fakes=n_fakes,
        )
        t2 = time.perf_counter()
        
        output_size = os.path.getsize(rwmod_path)
        logger.info(
            f"Pack complete: {input_size / 1024**2:.1f} MB -> "
            f"{output_size / 1024**2:.1f} MB "
            f"({100 * output_size / input_size:.0f}%)"
        )
        
        return {
            "zip_seconds":       round(t1 - t0, 3),
            "obfuscate_seconds": round(t2 - t1, 3),
            "input_size":        input_size,
            "output_size":       output_size,
            "protected":         True,
        }
    finally:
        if temp_zip and os.path.exists(temp_zip):
            try:
                os.remove(temp_zip)
                logger.debug(f"Cleaned temp ZIP")
            except OSError:
                pass


# ===========================================================================
# GUI
# ===========================================================================
class RepackerApp:
    """GUI for RWMod Repacker."""
    
    def __init__(self, root: tk.Tk):
        self.root = root
        root.title("RWMod Repacker")
        root.geometry("820x740")
        root.minsize(720, 660)
        
        # **THREAD-SAFE QUEUE FOR LOGGING**
        self.log_queue: Queue = Queue()
        
        main = ttk.Frame(root, padding=12)
        main.pack(fill="both", expand=True)
        
        ttk.Label(main, text="RWMod Repacker",
                  font=("Segoe UI", 16, "bold")).pack(anchor="w", pady=(0, 10))
        
        # --- Security Note ---
        note_frame = ttk.LabelFrame(main, text="ℹ️ Obfuscation Only (No Encryption)", padding=8)
        note_frame.pack(fill="x", pady=4)
        ttk.Label(note_frame, 
                  text="Prevents casual extraction. Rusted Warfare can still load. No password protection.",
                  foreground="blue").pack(anchor="w")
        
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
        
        # --- OUTPUT ---
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
        
        self.append_log("RWMod Repacker ready.")
        self.append_log("- Point Source at a FOLDER to Repack")
        self.append_log("- Point Source at a .rwmod FILE to Validate")
        self.append_log("")
        self.append_log("Security: Obfuscation only (no encryption). RW can read protected mods.")
        
        # Periodically check log queue
        self.check_log_queue()
    
    def check_log_queue(self) -> None:
        """Check for new log messages from background threads."""
        try:
            while True:
                msg = self.log_queue.get_nowait()
                self.append_log(msg)
        except:
            pass
        self.root.after(100, self.check_log_queue)
    
    def append_log(self, msg: str) -> None:
        """Append message to log window."""
        self.log.configure(state="normal")
        self.log.insert("end", msg + "\n")
        self.log.see("end")
        self.log.configure(state="disabled")
    
    def browse_folder(self) -> None:
        """Browse for source folder."""
        folder = filedialog.askdirectory(title="Select folder to pack")
        if folder:
            self.source_var.set(folder)
    
    def browse_file(self) -> None:
        """Browse for .rwmod file to validate."""
        file = filedialog.askopenfilename(
            title="Select .rwmod file to validate",
            filetypes=[("RWMOD files", "*.rwmod"), ("All files", "*.*")]
        )
        if file:
            self.source_var.set(file)
    
    def browse_output(self) -> None:
        """Browse for output folder."""
        folder = filedialog.askdirectory(title="Select output folder")
        if folder:
            self.output_var.set(folder)
    
    def start_validate(self) -> None:
        """Validate selected .rwmod file."""
        path = self.source_var.get().strip()
        if not path:
            messagebox.showerror("Error", "Please select a .rwmod file first")
            return
        
        self.validate_btn.config(state="disabled")
        self.repack_btn.config(state="disabled")
        
        def worker():
            try:
                self.append_log(f"\nValidating: {path}")
                report, is_valid = validate_rwmod_report(path)
                self.append_log(report)
                if is_valid:
                    self.status_var.set("✓ Validation complete - VALID")
                else:
                    self.status_var.set("✗ Validation complete - INVALID")
            except Exception as e:
                self.append_log(f"ERROR: {e}")
                self.status_var.set(f"Error: {e}")
                logger.exception("Validation failed")
            finally:
                self.validate_btn.config(state="normal")
                self.repack_btn.config(state="normal")
        
        t = threading.Thread(target=worker, daemon=True)
        t.start()
    
    def start_repack(self) -> None:
        """Repack selected folder."""
        folder = self.source_var.get().strip()
        output = self.output_var.get().strip()
        
        if not folder:
            messagebox.showerror("Error", "Please select a folder to pack")
            return
        if not output:
            messagebox.showerror("Error", "Please select an output folder")
            return
        if not os.path.isdir(output):
            messagebox.showerror("Error", f"Output folder doesn't exist: {output}")
            return
        
        self.validate_btn.config(state="disabled")
        self.repack_btn.config(state="disabled")
        self.progress.config(value=0)
        self.status_var.set("Scanning folder...")
        
        def progress_callback(stage: str, value: float) -> None:
            if stage in STAGE_WEIGHTS:
                w_min, w_max = STAGE_WEIGHTS[stage]
                overall = int(w_min + (w_max - w_min) * value)
                self.progress.config(value=overall)
                self.status_var.set(f"{stage}: {overall}%")
        
        def worker():
            try:
                # Scan folder
                report = scan_folder(folder)
                self.append_log(f"\nFolder scan:\n{report.summary()}")
                
                if report.warnings:
                    self.append_log("\n⚠️ Warnings detected - packing may fail")
                
                self.append_log(f"\nPacking {folder}...")
                
                rwmod_name = os.path.basename(folder.rstrip(os.sep)) + ".rwmod"
                rwmod_path = os.path.join(output, rwmod_name)
                
                result = pack_as_rwmod(folder, rwmod_path, callback=progress_callback)
                
                self.append_log(f"\n✓ SUCCESS")
                self.append_log(f"  Input:  {result['input_size'] / 1024**2:.1f} MB")
                self.append_log(f"  Output: {result['output_size'] / 1024**2:.1f} MB "
                               f"({100 * result['output_size'] / result['input_size']:.0f}%)")
                self.append_log(f"  ZIP time:       {result['zip_seconds']:.2f}s")
                self.append_log(f"  Obfuscate time: {result['obfuscate_seconds']:.2f}s")
                self.append_log(f"  Protected:      {result['protected']}")
                self.append_log(f"  Output: {rwmod_path}")
                
                self.status_var.set("✓ Packing complete")
                self.progress.config(value=100)
                messagebox.showinfo("Success", f"Packed to: {rwmod_path}")
            
            except Exception as e:
                self.append_log(f"\n✗ ERROR: {e}")
                self.status_var.set(f"Error: {type(e).__name__}")
                messagebox.showerror("Error", f"{type(e).__name__}: {e}")
                logger.exception("Packing failed")
            finally:
                self.validate_btn.config(state="normal")
                self.repack_btn.config(state="normal")
        
        t = threading.Thread(target=worker, daemon=True)
        t.start()


def main():
    """Launch GUI."""
    root = tk.Tk()
    app = RepackerApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
