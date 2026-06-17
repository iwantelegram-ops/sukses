"""
plugins/commands/unmutemic.py
──────────────────────────────
Perintah /unmutemic — minta inspeksi dadakan untuk membuka mute mic.

FLOW:
  1. User kirim /unmutemic di grup
  2. Hapus pesan perintah segera
  3. Cek anti-spam (cooldown 5 menit per user per grup)
  4. Cek apakah user ada di daftar yang pernah di-mute userbot (vc_muted_by_ub)
     → Tidak ada di daftar → abaikan
  5. Bot pemantau cek bio user secara fresh
     → Ada link → abaikan (user masih punya link, tidak di-unmute)
     → Tidak ada link / tidak bisa cek → lanjut ke langkah 6
  6. Hapus cache member user ini (agar non-member yang sudah join bisa dikenali)
  7. Jalankan inspeksi dadakan (userbot naik VC dan scan peserta)
     → Jika ada inspeksi lain sedang berjalan → tunggu / tambah jeda dulu
"""

import asyncio
import time

from pyrogram import Client, filters
from pyrogram.types import Message
from pyrogram.enums import ParseMode

from database import db

# ── Cooldown anti-spam: 5 menit per (chat_id, user_id) ─────────────────────
_unmutemic_cooldown: dict[tuple[int, int], float] = {}
_COOLDOWN_SECS = 300   # 5 menit


@Client.on_message(filters.command("unmutemic") & filters.group)
async def cmd_unmutemic(client: Client, message: Message):
    """
    Perintah /unmutemic di grup.
    Siapapun bisa pakai (untuk diri sendiri) — tidak perlu admin.
    """
    cid = message.chat.id
    uid = message.from_user.id if message.from_user else None
    if not uid:
        try:
            await message.delete()
        except Exception:
            pass
        return

    # ── Hapus pesan perintah segera ─────────────────────────────────────────
    try:
        await message.delete()
    except Exception:
        pass

    # ── Anti-spam: cek cooldown ──────────────────────────────────────────────
    now = time.time()
    last_used = _unmutemic_cooldown.get((cid, uid), 0.0)
    if now - last_used < _COOLDOWN_SECS:
        return   # masih cooldown → abaikan diam-diam

    # Set cooldown sebelum proses agar spam saat proses berjalan juga ditolak
    _unmutemic_cooldown[(cid, uid)] = now

    # ── Cek apakah user ada di daftar muted oleh userbot ────────────────────
    try:
        from video_call import (
            _ub_muted_this_user,
            _query_bio_from_db,
            _vc_scan_and_enforce,
            is_userbot_ready,
            get_vc_inspection_lock,
            _sec_os_get,
            _member_cache,
        )
    except ImportError as _e:
        print(f"[UnmuteMic] Import error dari video_call: {_e}")
        return

    was_muted = await _ub_muted_this_user(cid, uid)
    if not was_muted:
        # User tidak ada di daftar muted userbot → abaikan
        _unmutemic_cooldown.pop((cid, uid), None)   # kembalikan cooldown agar bisa coba lagi
        return

    # ── Cek apakah Security OS aktif untuk grup ini ──────────────────────────
    sec_doc = await _sec_os_get(cid)
    if not sec_doc.get("enabled"):
        return

    # ── Cek bio user via bot pemantau (fresh check) ──────────────────────────
    has_link = await _query_bio_from_db(cid, uid)

    if has_link is True:
        # User masih punya link di bio → tidak di-unmute, abaikan
        return

    # has_link=False (bio bersih) atau None (tidak bisa cek)
    # → lanjut inspeksi dadakan

    if not is_userbot_ready():
        # Userbot tidak aktif → tidak bisa inspeksi
        return

    # ── Invalidasi cache member agar re-check keanggotaan ────────────────────
    # Non-member yang sudah bergabung grup perlu dicek ulang oleh _is_group_member
    _member_cache.pop((cid, uid), None)

    # ── Jalankan inspeksi dadakan dengan global lock (cegah concurrent floodwait)
    asyncio.create_task(_run_inspeksi_dadakan(cid, get_vc_inspection_lock))


async def _run_inspeksi_dadakan(chat_id: int, get_lock_fn) -> None:
    """
    Jalankan _vc_scan_and_enforce dengan protection lock agar tidak berjalan
    bersamaan dengan inspeksi grup lain (menghindari Telegram FloodWait).

    Jika lock sedang dikuasai (inspeksi grup lain berjalan):
      → Tunggu hingga selesai (timeout 60 detik)
      → Jika timeout → tambah jeda 15 detik, lalu tetap jalankan
    """
    from video_call import _vc_scan_and_enforce

    lock = get_lock_fn()
    acquired = False
    try:
        acquired = await asyncio.wait_for(lock.acquire(), timeout=60.0)
    except asyncio.TimeoutError:
        # Tidak bisa dapat lock dalam 60 detik → jeda 15 detik lalu jalankan
        print(
            f"[UnmuteMic] Grup {chat_id}: inspeksi lain masih berjalan — "
            "jeda 15 detik sebelum inspeksi dadakan."
        )
        await asyncio.sleep(15)

    try:
        print(f"[UnmuteMic] Grup {chat_id}: memulai inspeksi dadakan via /unmutemic.")
        await _vc_scan_and_enforce(chat_id)
    except Exception as e:
        print(f"[UnmuteMic] Error inspeksi dadakan grup {chat_id}: {e}")
    finally:
        if acquired and lock.locked():
            try:
                lock.release()
            except RuntimeError:
                pass
