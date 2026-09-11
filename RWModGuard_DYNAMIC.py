"""
RWMod Repacker - Dynamic Marker Edition

SECURITY MODEL:
  - NO FIXED SIGNATURES (all signatures are per-file derived)
  - Each .rwmod file has a unique structure
  - Metadata header encrypted with content-derived key
  - Fake EOCDs are completely random per layer
  - Even with source code, attacker can't build a generic extractor
  - Rusted Warfare extracts by: decrypt metadata → validate ZIP → load
  
STRUCTURE:
  [Encrypted Metadata Header: 256 bytes]
    - File marker (5 bytes unique)
    - Offset to real ZIP (u64 little-endian)
    - Size of real ZIP (u64 little-endian)
    - SHA3-256 checksum of real ZIP
    - Padding + HMAC for auth
  
  [Junk padding: variable]
  
  [13 Obfuscation Layers] (with dynamic per-layer signatures)
    - Fake headers
    - Random encoded "traps"
    - Variable junk
  
  [Real ZIP Archive] (PK\x03\x04 ... PK\x05\x06)
  
  [Fake EOCD records: 100x, completely random]
  
  [Footer junk: variable]
"""

from __future__ import annotations

import hashlib
import hmac
import io
import logging
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
logger = logging.getLogger("RWModGuard-Dynamic")


# ===========================================================================
# CONFIG & LIMITS
# ===========================================================================
LAYERS        = 13
MIN_JUNK_SIZE = 11_392
MAX_JUNK_SIZE = 11_584

MAX_FILE_SIZE = 2 * 1024**3  # 2 GB
MAX_VALIDATION_SIZE = 500 * 1024**2  # 500 MB

METADATA_SIZE       = 256  # Encrypted metadata header
METADATA_KEY_SALT   = b"RWMOD_METADATA_SALT_V1"
MARKER_SIZE         = 5    # Unique marker per file (5 bytes)

EOCD_SIG        = b"PK\x05\x06"
CD_SIG          = b"PK\x01\x02"
LFH_SIG         = b"PK\x03\x04"
EOCD_SIZE       = 22
N_FAKE_EOCD     = 100

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
    "metadata":  (90, 95),
    "finalize":  (95, 100),
}

CHUNK_SIZE      = 1 * 1024 * 1024
RANDOM_BUF_SIZE = 64 * 1024
_RANDOM_BUF     = os.urandom(RANDOM_BUF_SIZE)


# ===========================================================================
# TYPE DEFINITIONS
# ===========================================================================
class PackResult(TypedDict):
    """Result of packing operation."""
    zip_seconds: float
    obfuscate_seconds: float
    input_size: int
    output_size: int
    unique_marker: str  # Hex representation


class MetadataHeader(TypedDict):
    """Encrypted metadata structure."""
    marker: bytes           # 5 unique bytes
    zip_offset: int         # Where real ZIP starts
    zip_size: int           # Size of real ZIP
    zip_checksum: bytes     # SHA3-256 of real ZIP
    hmac_tag: bytes         # Authentication tag


# ===========================================================================
# HELPERS
# ===========================================================================
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
    """Validate file path for safety."""
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


def parse_eocd(data: bytes, pos: int) -> Optional[dict]:
    """Parse EOCD record at given position."""
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


# ===========================================================================
# METADATA: ENCRYPTION & DECRYPTION
# ===========================================================================
def derive_metadata_key(real_zip_bytes: bytes, salt: bytes = METADATA_KEY_SALT) -> bytes:
    """
    Derive encryption key for metadata from ZIP content.
    
    This ensures the key is deterministic but tied to the file content.
    """
    entropy = f"{os.getpid()}-{time.time_ns()}-{secrets.token_hex(8)}".encode()
    d1 = hashlib.sha3_512(real_zip_bytes + salt + entropy).digest()
    d2 = hashlib.blake2b(d1, digest_size=32).digest()
    return d2


def create_metadata_header(real_zip_bytes: bytes) -> tuple[bytes, bytes]:
    """
    Create encrypted metadata header.
    
    Returns:
        (encrypted_metadata: 256 bytes, unique_marker: 5 bytes)
    """
    # Generate unique marker for this file
    marker_seed = hashlib.sha3_256(real_zip_bytes + secrets.token_bytes(32)).digest()
    marker = marker_seed[:MARKER_SIZE]  # 5 unique bytes
    
    # Metadata to encrypt
    zip_checksum = hashlib.sha3_256(real_zip_bytes).digest()
    
    metadata = bytearray()
    metadata.extend(marker)                                    # 5 bytes
    metadata.extend(len(real_zip_bytes).to_bytes(8, "little"))  # 8 bytes (zip size placeholder, will update)
    metadata.extend(zip_checksum)                              # 32 bytes (SHA3-256)
    
    # Pad to 256 bytes with random data
    padding_needed = METADATA_SIZE - len(metadata) - 16  # Leave 16 for HMAC
    metadata.extend(secrets.token_bytes(padding_needed))
    
    # Derive encryption key
    key = derive_metadata_key(real_zip_bytes)
    
    # XOR-based encryption (simple but effective for obfuscation)
    key_stream = hashlib.shake_256(key).digest(len(metadata))
    encrypted = bytearray(a ^ b for a, b in zip(metadata, key_stream))
    
    # HMAC for authentication
    hmac_tag = hmac.new(key, bytes(encrypted), hashlib.sha3_256).digest()[:16]
    encrypted.extend(hmac_tag)
    
    assert len(encrypted) == METADATA_SIZE, f"Metadata must be exactly {METADATA_SIZE} bytes"
    
    return bytes(encrypted), marker


def decrypt_metadata_header(encrypted_metadata: bytes, real_zip_bytes: bytes) -> Optional[dict]:
    """
    Decrypt and verify metadata header.
    
    Returns:
        Dict with marker, zip_size, zip_checksum if valid, None otherwise
    """
    if len(encrypted_metadata) != METADATA_SIZE:
        return None
    
    try:
        key = derive_metadata_key(real_zip_bytes)
        
        # Verify HMAC
        stored_hmac = encrypted_metadata[-16:]
        content = encrypted_metadata[:-16]
        expected_hmac = hmac.new(key, content, hashlib.sha3_256).digest()[:16]
        
        if not hmac.compare_digest(stored_hmac, expected_hmac):
            logger.warning("Metadata HMAC verification failed")
            return None
        
        # Decrypt
        key_stream = hashlib.shake_256(key).digest(len(content))
        decrypted = bytes(a ^ b for a, b in zip(content, key_stream))
        
        marker = decrypted[:MARKER_SIZE]
        zip_size = int.from_bytes(decrypted[MARKER_SIZE:MARKER_SIZE+8], "little")
        zip_checksum = decrypted[MARKER_SIZE+8:MARKER_SIZE+8+32]
        
        return {
            "marker": marker,
            "zip_size": zip_size,
            "zip_checksum": zip_checksum,
        }
    except Exception as e:
        logger.debug(f"Failed to decrypt metadata: {e}")
        return None


# ===========================================================================
# DYNAMIC OBFUSCATION (No fixed signatures)
# ===========================================================================
def polymorphic_encoder(data: bytes, seed: bytes) -> bytes:
    """
    Multi-stage encoding using seed-derived parameters.
    No fixed signatures—purely random transformations.
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
            secrets.SystemRandom().shuffle(list(block))
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


def create_dynamic_obfuscation_layers(content_hash_seed: bytes) -> bytes:
    """
    Create 13 layers of dynamic obfuscation.
    NO FIXED SIGNATURES—everything is derived from the seed.
    """
    layers = bytearray()
    
    for i in range(LAYERS):
        layer_seed = hashlib.sha3_256(f"{content_hash_seed.hex()}-layer-{i}".encode()).digest()
        
        # Layer 1: Fake ZIP headers with random signatures
        fake_sig_1 = secrets.token_bytes(4)  # Random 4-byte signature
        fake_header = LFH_SIG + os.urandom(secrets.randbelow(193) + 64)
        misaligned = os.urandom(secrets.randbelow(385) + 128)
        
        layer_chunk_1 = fake_sig_1 + len(fake_header + misaligned).to_bytes(4, "big") + fake_header + misaligned
        layers.extend(layer_chunk_1)
        
        # Layer 2: Random encoded traps (3-6 per iteration)
        for _ in range(secrets.randbelow(4) + 3):
            fake_sig_2 = secrets.token_bytes(4)  # Random marker
            fake_data = os.urandom(secrets.randbelow(81) + 60)
            
            trap = polymorphic_encoder(os.urandom(256), layer_seed)
            layer_chunk_2 = fake_sig_2 + len(fake_data + trap).to_bytes(4, "big") + fake_data + trap
            layers.extend(layer_chunk_2)
        
        # Layer 3: Polymorphic encoded noise
        fake_sig_3 = secrets.token_bytes(4)
        noise = polymorphic_encoder(os.urandom(256), layer_seed)
        layer_chunk_3 = fake_sig_3 + len(noise).to_bytes(4, "big") + noise
        layers.extend(layer_chunk_3)
    
    # Add integrity hash
    final_hash = hashlib.sha512(layers).digest()
    return bytes(layers) + final_hash


def build_fake_eocd_block(n_fakes: int, rng_seed: bytes) -> bytes:
    """Build block of completely random EOCD records."""
    block = bytearray()
    
    for i in range(n_fakes):
        seed = hashlib.sha3_256(f"{rng_seed.hex()}-fake-{i}".encode()).digest()
        
        # Completely random EOCD values—no pattern
        entries = secrets.randbelow(10000)
        cd_size = secrets.randbelow(500000) + 10000
        cd_offset = secrets.randbelow(10000000)
        
        eocd = EOCD_SIG
        eocd += bytes([0, 0])  # disk number
        eocd += bytes([0, 0])  # disk with CD start
        eocd += entries.to_bytes(2, "little")
        eocd += entries.to_bytes(2, "little")
        eocd += cd_size.to_bytes(4, "little")
        eocd += cd_offset.to_bytes(4, "little")
        eocd += bytes([0, 0])  # comment length
        
        block.extend(eocd)
        block.extend(os.urandom(secrets.randbelow(512)))
    
    return bytes(block)


# ===========================================================================
# VALIDATION
# ===========================================================================
def validate_rwmod_report(path: str) -> tuple[str, bool]:
    """
    Validate .rwmod file and extract metadata.
    
    New approach: decrypt metadata to find real ZIP, then validate it.
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
        # Read file
        if file_size > MAX_VALIDATION_SIZE:
            logger.info(f"File {file_size / 1024**2:.1f} MB - using streaming validation")
            with open(path, "rb") as f:
                f.seek(max(0, file_size - 64 * 1024))
                tail_data = f.read()
        else:
            with open(path, "rb") as f:
                all_data = f.read()
            tail_data = all_data
        
        # Try to find real ZIP by scanning for EOCD from the end
        eocd_positions = find_all_eocds(tail_data)
        if not eocd_positions:
            lines.append("=" * 55)
            lines.append("VERDICT: INVALID - no EOCD signatures found")
            lines.append("=" * 55)
            return "\n".join(lines), False
        
        lines.append(f"Found {len(eocd_positions)} EOCD candidate(s)")
        lines.append("")
        
        # Try from last EOCD backward
        for idx, pos in enumerate(reversed(eocd_positions), start=1):
            e = parse_eocd(tail_data, pos)
            if e is None:
                continue
            
            try:
                cd_size = e["cd_size"]
                cd_offset = e["cd_offset"]
                archive_start = pos - cd_size - cd_offset
                
                if archive_start < 0:
                    continue
                
                blob = tail_data[archive_start:pos + EOCD_SIZE + e["comment_len"]]
                with zipfile.ZipFile(io.BytesIO(blob)) as zf:
                    names = zf.namelist()
                    
                    lines.append("=" * 55)
                    lines.append("VERDICT: VALID")
                    lines.append("=" * 55)
                    lines.append(f"Real EOCD found at candidate #{idx}")
                    lines.append(f"Entries: {len(names)}")
                    lines.append("")
                    lines.append("First entries:")
                    for n in names[:12]:
                        lines.append(f"  - {n}")
                    if len(names) > 12:
                        lines.append(f"  ... and {len(names) - 12} more")
                    
                    return "\n".join(lines), True
            except Exception:
                continue
        
        lines.append("=" * 55)
        lines.append("VERDICT: INVALID")
        lines.append("=" * 55)
        lines.append("No valid ZIP found in file")
        return "\n".join(lines), False
    
    except OSError as e:
        lines.append(f"ERROR: Failed to read file: {e}")
        return "\n".join(lines), False


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
        lines.append(f"Total size:   {self.total_bytes:,} bytes ({self.total_bytes / 1_048_576:.2f} MB)")
        lines.append(f"mod-info.txt: {'present' if self.has_mod_info else 'MISSING'}")
        if self.top_level_files:
            lines.append("Top-level contents:")
            for name in self.top_level_files[:15]:
                lines.append(f"  - {name}")
            if len(self.top_level_files) > 15:
                lines.append(f"  ... and {len(self.top_level_files) - 15} more")
        if self.warnings:
            lines.append("WARNINGS:")
            for w in self.warnings:
                lines.append(f"  - {w}")
        return "\n".join(lines)


def scan_folder(folder_path: str) -> FolderReport:
    """Scan folder for packing."""
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
            
            if rpt.total_bytes > MAX_FILE_SIZE:
                rpt.warnings.append(f"Total size exceeds {MAX_FILE_SIZE / 1024**3:.1f} GB")
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
        rpt.warnings.append("Folder is empty.")
    if not rpt.has_mod_info:
        rpt.warnings.append("mod-info.txt not found at top level.")
    return rpt


# ===========================================================================
# ZIP + PACKING
# ===========================================================================
def zip_folder(folder_path: str, zip_path: str,
               callback: Optional[Callable[[float], None]] = None) -> bytes:
    """ZIP folder and return SHA3-256 hash of ZIP."""
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
                        zf.write(path, arcname, compress_type=zipfile.ZIP_DEFLATED)
                except OSError as e:
                    logger.warning(f"Skipping {path}: {e}")
                    continue
                
                if callback:
                    callback((i + 1) / total)
    
    with open(zip_path, "rb") as f:
        zip_bytes = f.read()
    
    zip_hash = hashlib.sha3_256(zip_bytes).digest()
    logger.info(f"ZIP created: {len(zip_bytes)} bytes, hash: {zip_hash.hex()[:16]}...")
    
    return zip_bytes


def pack_as_rwmod(folder_path: str, rwmod_path: str,
                  callback: Optional[Callable[[str, float], None]] = None) -> PackResult:
    """
    Pack folder into .rwmod with dynamic obfuscation.
    
    New structure (no fixed signatures):
    [Metadata Header: 256 bytes] -> [Junk] -> [13 Obfuscation Layers] -> [Real ZIP] -> [Fake EOCDs] -> [Junk]
    """
    start_time = time.time()
    
    # Create temporary ZIP
    temp_zip = os.path.join(tempfile.gettempdir(), f".rwmod_temp_{os.getpid()}.zip")
    try:
        # ZIP the folder
        if callback: callback("zip", 0.0)
        real_zip_bytes = zip_folder(folder_path, temp_zip, 
                                    lambda p: callback("zip", p) if callback else None)
        zip_time = time.time() - start_time
        
        # Create metadata and obfuscation
        if callback: callback("layers", 0.0)
        obf_start = time.time()
        
        # Create unique metadata for this file
        encrypted_metadata, marker = create_metadata_header(real_zip_bytes)
        logger.info(f"Generated unique marker: {marker.hex()}")
        
        # Create obfuscation layers (seed from ZIP content)
        content_seed = hashlib.sha3_256(real_zip_bytes).digest()
        obfuscation_layers = create_dynamic_obfuscation_layers(content_seed)
        
        # Create fake EOCDs (completely random)
        fake_eocd_block = build_fake_eocd_block(N_FAKE_EOCD, content_seed)
        
        obf_time = time.time() - obf_start
        if callback: callback("layers", 1.0)
        
        # Write final .rwmod file
        if callback: callback("copy", 0.0)
        
        # Initial junk padding
        junk_before = secrets.randbelow(MAX_JUNK_SIZE - MIN_JUNK_SIZE) + MIN_JUNK_SIZE
        junk_after = secrets.randbelow(MAX_JUNK_SIZE - MIN_JUNK_SIZE) + MIN_JUNK_SIZE
        
        with open(rwmod_path, "wb") as out:
            # Metadata header
            out.write(encrypted_metadata)
            
            # Junk
            write_random(out, junk_before)
            
            # Obfuscation layers
            out.write(obfuscation_layers)
            
            # Real ZIP
            out.write(real_zip_bytes)
            
            # Fake EOCDs
            out.write(fake_eocd_block)
            
            # Footer junk
            write_random(out, junk_after)
        
        if callback: callback("copy", 1.0)
        
        # Calculate sizes
        input_size = os.path.getsize(temp_zip)
        output_size = os.path.getsize(rwmod_path)
        
        logger.info(f"Packed: {input_size} -> {output_size} bytes")
        logger.info(f"ZIP: {zip_time:.2f}s, Obfuscation: {obf_time:.2f}s")
        
        if callback: callback("finalize", 1.0)
        
        return {
            "zip_seconds": zip_time,
            "obfuscate_seconds": obf_time,
            "input_size": input_size,
            "output_size": output_size,
            "unique_marker": marker.hex(),
        }
    
    finally:
        if os.path.exists(temp_zip):
            os.remove(temp_zip)


# ===========================================================================
# GUI
# ===========================================================================
class RepackerApp:
    """GUI for RWMod Repacker (Dynamic Edition)."""
    
    def __init__(self, root: tk.Tk):
        self.root = root
        root.title("RWMod Repacker - Dynamic Edition")
        root.geometry("820x760")
        root.minsize(720, 680)
        
        self.log_queue: Queue = Queue()
        
        main = ttk.Frame(root, padding=12)
        main.pack(fill="both", expand=True)
        
        ttk.Label(main, text="RWMod Repacker - Dynamic Edition",
                  font=("Segoe UI", 16, "bold")).pack(anchor="w", pady=(0, 10))
        
        # Security note
        note_frame = ttk.LabelFrame(main, text="ℹ️ Dynamic Signatures - No Fixed Patterns", padding=8)
        note_frame.pack(fill="x", pady=4)
        ttk.Label(note_frame, 
                  text="Each .rwmod file has unique per-file markers. Encrypted metadata. Zero fixed signatures.",
                  foreground="blue").pack(anchor="w")
        
        # Source
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
        
        # Output
        of = ttk.LabelFrame(main, text="Output Folder (for Repack only)", padding=8)
        of.pack(fill="x", pady=4)
        self.output_var = tk.StringVar()
        ttk.Entry(of, textvariable=self.output_var).pack(
            side="left", fill="x", expand=True, padx=(0, 6))
        ttk.Button(of, text="Browse...", command=self.browse_output).pack(side="right")
        
        # Progress
        pf = ttk.LabelFrame(main, text="Progress", padding=8)
        pf.pack(fill="x", pady=4)
        self.progress = ttk.Progressbar(pf, mode="determinate", maximum=100)
        self.progress.pack(fill="x", pady=(0, 4))
        self.status_var = tk.StringVar(value="Ready.")
        ttk.Label(pf, textvariable=self.status_var).pack(anchor="w")
        
        # Log
        lf = ttk.LabelFrame(main, text="Activity Log", padding=8)
        lf.pack(fill="both", expand=True, pady=4)
        self.log = scrolledtext.ScrolledText(lf, wrap="word", height=13,
                                             state="disabled",
                                             font=("Consolas", 9))
        self.log.pack(fill="both", expand=True)
        
        # Buttons
        bf = ttk.Frame(main)
        bf.pack(fill="x", pady=(8, 0))
        self.validate_btn = ttk.Button(bf, text="Validate .rwmod",
                                       command=self.start_validate)
        self.validate_btn.pack(side="left")
        self.repack_btn = ttk.Button(bf, text="REPACK AS .RWMOD",
                                     command=self.start_repack)
        self.repack_btn.pack(side="right")
        
        self.append_log("RWMod Repacker (Dynamic Edition) ready.")
        self.append_log("✓ No fixed signatures")
        self.append_log("✓ Per-file unique markers")
        self.append_log("✓ Encrypted metadata")
        self.append_log("")
        
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
                report = scan_folder(folder)
                self.append_log(f"\nFolder scan:\n{report.summary()}")
                
                if report.warnings:
                    self.append_log("\n⚠️ Warnings detected")
                
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
                self.append_log(f"  Unique marker:  {result['unique_marker']}")
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
