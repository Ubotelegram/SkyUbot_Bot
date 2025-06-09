import asyncio
import json
import logging
import os
import time
import gc
import re
import collections
from collections import defaultdict, OrderedDict
from uuid import uuid4
import asyncpg
from telethon import TelegramClient, events, Button
from telethon.sessions import StringSession
from telethon.errors import (
    SessionPasswordNeededError,
    FloodWaitError,
    MessageNotModifiedError,
    AuthKeyUnregisteredError,
    SessionRevokedError,
    UserDeactivatedBanError,
    ChannelsTooMuchError,
    PhoneCodeInvalidError,
    UsernameNotOccupiedError,
    UsernameInvalidError,
    ChannelPrivateError,
    ChatAdminRequiredError,
    UserIsBlockedError,
    MsgIdInvalidError,
    ChatWriteForbiddenError,
    ChatRestrictedError, 
    UserBannedInChannelError,
    UserChannelsTooMuchError,
    RpcCallFailError,
    BotMethodInvalidError,
    UserNotMutualContactError,
    UserPrivacyRestrictedError
)
from telethon.tl.types import MessageEntityBlockquote, MessageEntitySpoiler, MessageEntityTextUrl, MessageEntityCustomEmoji
from telethon.tl.types import Channel, Chat, PeerUser, PeerChat, PeerChannel
from telethon.tl import functions
from telethon.utils import get_peer_id 
import copy
import datetime

# --- Konfigurasi Logging ---
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(filename)s:%(lineno)d - %(message)s',
    handlers=[
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)
logging.getLogger('telethon').setLevel(logging.WARNING)

# --- Konfigurasi Utama ---
ADMIN_IDS = [, ] 
API_ID = os.environ.get('API_ID', '')
API_HASH = os.environ.get('API_HASH', '')
BOT_TOKEN = os.environ.get('BOT_TOKEN', '') 
WELCOME_IMAGE_URL = os.environ.get('WELCOME_IMAGE_URL', '') 
KEY_PURCHASE_CONTACT = os.environ.get('KEY_PURCHASE_CONTACT', '') 

# --- Konfigurasi Database ---
DATABASE_URL = os.environ.get('DATABASE_URL', '') 
POOL_MIN_SIZE = 1
POOL_MAX_SIZE = 10 
RETRY_ATTEMPTS = 5
RETRY_DELAY = 3.0

# --- Konfigurasi Lainnya ---
BATCH_SIZE = 50
BATCH_DELAY = 5
ITEMS_PER_PAGE = 5 
ADMIN_KEYS_ITEMS_PER_PAGE = 7 
CACHE_TTL = 300
ENTITY_CACHE_SIZE = 100
KEY_CHECK_INTERVAL = 300 

# --- Konfigurasi Watermark Default ---
DEFAULT_GLOBAL_WATERMARK_TEXT = "Dikirim melalui HARA11Z X BOT"

# --- Default User Data ---
DEFAULT_BOT_DATA = {
    'saved_texts': [],
    'delay': 120, # Delay global
    'is_copying': False,
    'target_groups': [],
    'awaiting_input_type': None,
    'awaiting_2fa': False,
    'is_registered': False, 
    'welcome_message_sent': False,
    'current_page_context': {},
    'watermark_enabled': False, 
    'watermark_text': DEFAULT_GLOBAL_WATERMARK_TEXT, 
    'active_key_value': None,
    'active_key_type': None, 
    'key_expiry_timestamp': None,
    'assigned_basic_watermark_text': None, 
    'has_valid_key': False, 
    # State untuk fitur baru
    'is_forwarding': False,
    'forward_sets': [], # Menyimpan dict single/dual link
    'forward_expiry_timestamp': None,
    'copy_expiry_timestamp': None,
    'admin_temp_key_type': None, 
    'admin_temp_key_duration_s': None,
    'admin_message_to_edit_id': None,
    'temp_dual_link_data': {}, # Untuk menyimpan data sementara saat membuat dual link
}

# --- State Global ---
user_clients = {}
user_tasks = {}
user_data_cache = {}
entity_cache = collections.OrderedDict()
db_pool = None
warning_counts = collections.defaultdict(int)
MAX_WARNINGS = 5

loop = asyncio.new_event_loop()
asyncio.set_event_loop(loop)
bot = TelegramClient(StringSession(""), API_ID, API_HASH, loop=loop, connection_retries=5, device_model="HARA11Z_KEYBOT_V3", system_version="16GRM", app_version="1.2.0_KeySysFix")

# --- Fungsi Helper Admin & Key ---
def is_admin(chat_id):
    return chat_id in ADMIN_IDS

def generate_unique_key(prefix="KEY-"):
    return prefix + uuid4().hex[:12].upper()

def parse_duration_to_seconds(duration_str):
    duration_str = duration_str.lower().strip()
    if duration_str.endswith('d'):
        try: return int(duration_str[:-1]) * 24 * 60 * 60
        except ValueError: return None
    elif duration_str.endswith('h'):
        try: return int(duration_str[:-1]) * 60 * 60
        except ValueError: return None
    elif duration_str.endswith('m'): 
        try: return int(duration_str[:-1]) * 60
        except ValueError: return None
    return None

# --- Fungsi Entity & Database ---
def entity_to_dict(entity):
    if entity is None: return None
    if isinstance(entity, dict): return entity
    entity_dict = {'type': type(entity).__name__, 'offset': entity.offset, 'length': entity.length}
    if isinstance(entity, MessageEntityTextUrl): entity_dict['url'] = entity.url
    elif isinstance(entity, MessageEntityCustomEmoji): entity_dict['document_id'] = entity.document_id
    return entity_dict

def dict_to_entity(entity_dict):
    if not isinstance(entity_dict, dict):
        logger.error(f"dict_to_entity menerima input non-dict: {entity_dict}")
        return None
    entity_type = entity_dict.get('type')
    offset, length = entity_dict.get('offset'), entity_dict.get('length')
    if entity_type == 'MessageEntityBlockquote': return MessageEntityBlockquote(offset, length)
    if entity_type == 'MessageEntitySpoiler': return MessageEntitySpoiler(offset, length)
    if entity_type == 'MessageEntityTextUrl': return MessageEntityTextUrl(offset, length, entity_dict.get('url'))
    if entity_type == 'MessageEntityCustomEmoji': return MessageEntityCustomEmoji(offset, length, entity_dict.get('document_id', 0))
    return None

async def init_db():
    global db_pool
    for attempt in range(RETRY_ATTEMPTS):
        try:
            db_pool = await asyncpg.create_pool(DATABASE_URL, min_size=POOL_MIN_SIZE, max_size=POOL_MAX_SIZE, command_timeout=30, max_queries=1000, max_inactive_connection_lifetime=180)
            async with db_pool.acquire() as conn:
                await conn.execute('''
                    CREATE TABLE IF NOT EXISTS users (
                        chat_id BIGINT PRIMARY KEY,
                        phone_number TEXT,
                        session_string TEXT,
                        bot_data JSONB
                    )
                ''')
                await conn.execute('''
                    CREATE TABLE IF NOT EXISTS access_keys (
                        key_value TEXT PRIMARY KEY,
                        key_type TEXT NOT NULL, 
                        duration_seconds BIGINT NOT NULL,
                        is_claimed BOOLEAN DEFAULT FALSE,
                        claimed_by_chat_id BIGINT,
                        claim_timestamp BIGINT,
                        original_expiry_timestamp BIGINT, 
                        generated_by_admin_id BIGINT NOT NULL,
                        generation_timestamp BIGINT NOT NULL,
                        assigned_watermark_text TEXT, 
                        notes TEXT 
                    )
                ''')
                await conn.execute('CREATE INDEX IF NOT EXISTS idx_access_keys_claimed_by ON access_keys(claimed_by_chat_id)')
            logger.info("Database berhasil diinisialisasi dan tabel diperiksa/dibuat.")
            return
        except Exception as e:
            logger.error(f"Inisialisasi DB percobaan {attempt+1} gagal: {e}", exc_info=True)
            if attempt < RETRY_ATTEMPTS - 1: await asyncio.sleep(RETRY_DELAY)
            else: logger.critical("Semua percobaan inisialisasi DB gagal."); raise

async def save_user_data(chat_id, phone_number=None, session_string=None, bot_data=None):
    for attempt in range(RETRY_ATTEMPTS):
        try:
            async with db_pool.acquire() as conn:
                existing_db_row = await conn.fetchrow('SELECT phone_number, session_string, bot_data FROM users WHERE chat_id = $1 FOR UPDATE', chat_id)
                db_phone, db_session, db_bot_data_json = (existing_db_row['phone_number'], existing_db_row['session_string'], existing_db_row['bot_data']) if existing_db_row else (None, None, None)
                
                db_bot_data_dict = {}
                if db_bot_data_json:
                    try: db_bot_data_dict = json.loads(db_bot_data_json)
                    except json.JSONDecodeError: logger.warning(f"JSON tidak valid di DB untuk {chat_id}")
                
                final_phone = phone_number if phone_number is not None else db_phone
                final_session = session_string if session_string is not None else db_session
                
                final_bot_data = copy.deepcopy(DEFAULT_BOT_DATA) 
                final_bot_data.update(db_bot_data_dict) 
                if bot_data is not None: final_bot_data.update(bot_data)

                current_keys = set(final_bot_data.keys())
                default_keys = set(DEFAULT_BOT_DATA.keys())

                for key_to_add in default_keys - current_keys:
                    final_bot_data[key_to_add] = copy.deepcopy(DEFAULT_BOT_DATA[key_to_add])
                
                for key_to_remove in current_keys - default_keys:
                    del final_bot_data[key_to_remove]
                
                final_bot_data_json_save = json.dumps(final_bot_data, separators=(',', ':'))
                
                if existing_db_row:
                    await conn.execute(
                        'UPDATE users SET phone_number = $2, session_string = $3, bot_data = $4 WHERE chat_id = $1',
                        chat_id, final_phone, final_session, final_bot_data_json_save
                    )
                else:
                    await conn.execute(
                        'INSERT INTO users (chat_id, phone_number, session_string, bot_data) VALUES ($1, $2, $3, $4)',
                        chat_id, final_phone, final_session, final_bot_data_json_save
                    )
                
                user_data_cache[chat_id] = (time.time(), final_phone, final_session, final_bot_data)
                return
        except Exception as e:
            logger.error(f"Simpan data percobaan {attempt+1} untuk {chat_id} gagal: {e}", exc_info=True)
            if attempt < RETRY_ATTEMPTS - 1: await asyncio.sleep(RETRY_DELAY)
            else: logger.critical(f"Semua percobaan menyimpan data untuk {chat_id} gagal.")
        return

async def load_user_data(chat_id):
    for attempt in range(RETRY_ATTEMPTS):
        try:
            async with db_pool.acquire() as conn:
                row = await conn.fetchrow('SELECT phone_number, session_string, bot_data FROM users WHERE chat_id = $1', chat_id)
                current_bot_data = copy.deepcopy(DEFAULT_BOT_DATA)
                phone_to_return, session_to_return = None, None

                if row:
                    phone_to_return = row['phone_number']
                    session_to_return = row['session_string']
                    if row['bot_data']:
                        try: 
                            loaded_db_data = json.loads(row['bot_data'])
                            for key in DEFAULT_BOT_DATA:
                                if key in loaded_db_data:
                                    current_bot_data[key] = loaded_db_data[key]
                        except json.JSONDecodeError: logger.error(f"Error decode JSON untuk {chat_id}. Menggunakan data default.")
                    
                    made_changes = False
                    for key, default_value in DEFAULT_BOT_DATA.items():
                        if key not in current_bot_data:
                            current_bot_data[key] = copy.deepcopy(default_value)
                            made_changes = True
                    
                    keys_in_loaded_data = list(current_bot_data.keys())
                    for key_in_loaded in keys_in_loaded_data:
                        if key_in_loaded not in DEFAULT_BOT_DATA:
                            del current_bot_data[key_in_loaded]
                            made_changes = True

                    if made_changes:
                        logger.info(f"Skema data pengguna {chat_id} diperbarui/dibersihkan. Menyimpan struktur baru.")
                        await save_user_data(chat_id, phone_number=phone_to_return, session_string=session_to_return, bot_data=current_bot_data)
                    
                    return phone_to_return, session_to_return, current_bot_data
                
                logger.info(f"Tidak ada data untuk {chat_id}. Membuat pengguna baru dengan data default.")
                await save_user_data(chat_id, bot_data=current_bot_data)
                return None, None, current_bot_data
        except Exception as e:
            logger.error(f"Muat data percobaan {attempt+1} untuk {chat_id} gagal: {e}", exc_info=True)
            if attempt < RETRY_ATTEMPTS - 1: await asyncio.sleep(RETRY_DELAY)
            else:
                logger.critical(f"Semua percobaan memuat data untuk {chat_id} gagal. Mengembalikan default in-memory.")
                return None, None, copy.deepcopy(DEFAULT_BOT_DATA)

async def get_user_data(chat_id):
    current_time = time.time()
    if chat_id in user_data_cache:
        timestamp, phone, session, bot_data_cache = user_data_cache[chat_id]
        if current_time - timestamp < CACHE_TTL:
            needs_refresh = False
            temp_bot_data = bot_data_cache.copy()
            for key, default_value in DEFAULT_BOT_DATA.items():
                if key not in temp_bot_data:
                    temp_bot_data[key] = copy.deepcopy(default_value)
                    needs_refresh = True 
            
            cached_keys = set(temp_bot_data.keys())
            default_keys = set(DEFAULT_BOT_DATA.keys())
            if cached_keys - default_keys: 
                needs_refresh = True

            if not needs_refresh:
                return phone, session, temp_bot_data
            else:
                logger.info(f"Cache untuk {chat_id} perlu penyegaran skema.")
    
    phone, session, bot_data_db = await load_user_data(chat_id)
    user_data_cache[chat_id] = (time.time(), phone, session, bot_data_db)
    return phone, session, bot_data_db

async def update_user_data_db(chat_id, phone_number=None, session_string=None, bot_data_update=None):
    current_phone, current_session, current_bot_data = await get_user_data(chat_id)
    final_phone = phone_number if phone_number is not None else current_phone
    final_session = session_string if session_string is not None else current_session
    updated_bot_data = current_bot_data.copy() 
    if bot_data_update: 
        for key, value in bot_data_update.items():
            if key in DEFAULT_BOT_DATA: 
                 updated_bot_data[key] = value
            else:
                logger.warning(f"Mencoba memperbarui/menambah kunci tidak dikenal '{key}' ke bot_data untuk {chat_id}. Kunci ini akan disimpan tapi mungkin tidak digunakan oleh DEFAULT_BOT_DATA.")
                updated_bot_data[key] = value 
    await save_user_data(chat_id, phone_number=final_phone, session_string=final_session, bot_data=updated_bot_data)

# --- Fungsi Menu ---
def main_menu(bot_data):
    key_type = bot_data.get('active_key_type', 'Tidak Ada')
    expiry_ts = bot_data.get('key_expiry_timestamp')
    expiry_str = f" (Kadaluwarsa: {datetime.datetime.fromtimestamp(expiry_ts).strftime('%Y-%m-%d %H:%M')})" if expiry_ts and expiry_ts > time.time() else " (Kadaluwarsa)" if expiry_ts else ""
    
    status_text = (
        f"Status Kunci: {key_type.capitalize()}{expiry_str}\n"
        f"Forward: {'AKTIF' if bot_data.get('is_forwarding', False) else 'NONAKTIF'}\n"
        f"Copy: {'AKTIF' if bot_data.get('is_copying', False) else 'NONAKTIF'}\n"
        f"Delay Global: {bot_data.get('delay', 120)} detik"
    )
    
    watermark_enabled_by_user = bot_data.get('watermark_enabled', False)
    is_vip = key_type == 'vip'
    assigned_basic_wm = bot_data.get('assigned_basic_watermark_text')

    if is_vip:
        status_text += f"\nWatermark (VIP): {'AKTIF' if watermark_enabled_by_user else 'NONAKTIF'}"
    elif key_type == 'basic' and assigned_basic_wm:
        status_text += f"\nWatermark (Dasar): AKTIF (Diatur Admin)"
    elif key_type == 'basic' and not assigned_basic_wm:
        status_text += f"\nWatermark (Dasar): NONAKTIF (Tidak ada teks dari Admin)"

    buttons = [
        [Button.inline("Pengaturan Forward & Copy", b"forward_copy_menu"), Button.inline("Set Delay Global", b"set_delay")],
        [Button.inline("Simpan Link Forward", b"save_link"), Button.inline("Hapus Link Forward", b"delete_link")],
        [Button.inline("Simpan Teks/Media", b"save_text_media"), Button.inline("Hapus Teks/Media", b"delete_text_media")],
        [Button.inline("Tambah Grup Target", b"add_group"), Button.inline("Hapus Grup Target", b"delete_group")],
    ]
    if is_vip: 
        buttons.append([Button.inline("💧 Pengaturan Watermark", b"watermark_settings")])
    return status_text, buttons

def forward_copy_menu(bot_data):
    fwd_expiry = bot_data.get('forward_expiry_timestamp')
    copy_expiry = bot_data.get('copy_expiry_timestamp')
    
    fwd_status = 'AKTIF' if bot_data.get('is_forwarding', False) else 'NONAKTIF'
    if fwd_expiry and fwd_status == 'AKTIF':
        fwd_status += f" (Berakhir: {datetime.datetime.fromtimestamp(fwd_expiry).strftime('%H:%M:%S')})"
        
    copy_status = 'AKTIF' if bot_data.get('is_copying', False) else 'NONAKTIF'
    if copy_expiry and copy_status == 'AKTIF':
        copy_status += f" (Berakhir: {datetime.datetime.fromtimestamp(copy_expiry).strftime('%H:%M:%S')})"

    text = f"Forward: {fwd_status}\nCopy: {copy_status}"
    buttons = [
        [Button.inline("Forward ON (Berwaktu)", b"forward_on"), Button.inline("Forward OFF", b"forward_off")],
        [Button.inline("Copy ON (Berwaktu)", b"copy_on"), Button.inline("Copy OFF", b"copy_off")],
        [Button.inline("Kembali ke Menu Utama", b"main_menu")]
    ]
    return text, buttons

def admin_main_menu():
    buttons = [
        [Button.inline("🔑 Kelola Kunci Akses", b"admin_manage_keys")],
        [Button.inline("📢 Broadcast Pesan", b"admin_broadcast")],
        [Button.inline("📊 Lihat Pengguna Aktif", b"admin_list_active_users")],
        [Button.inline("📱 Setup Userbot Pribadi (Admin)", b"admin_setup_userbot_prompt")] 
    ]
    return "👑 Panel Admin 👑", buttons

def admin_manage_keys_menu():
    buttons = [
        [Button.inline("➕ Buat Kunci Baru", b"admin_generate_key_prompt")],
        [Button.inline("📄 Daftar Kunci Belum Diklaim", b"admin_list_unclaimed_keys")],
        [Button.inline("👤 Daftar Kunci Diklaim", b"admin_list_claimed_keys")],
        [Button.inline("🗑️ Cabut/Hapus Kunci", b"admin_revoke_key_input")],
        [Button.inline("Kembali ke Panel Admin", b"admin_panel")]
    ]
    return "🔑 Manajemen Kunci Akses:", buttons

def watermark_settings_menu(bot_data): 
    status_wm = "AKTIF" if bot_data.get('watermark_enabled', False) else "NONAKTIF"
    current_text_wm = bot_data.get('watermark_text', DEFAULT_GLOBAL_WATERMARK_TEXT)
    if len(current_text_wm) > 50: current_text_wm = current_text_wm[:47] + "..."

    text = (
        f"--- Pengaturan Watermark (VIP) ---\n"
        f"Status: {status_wm}\n"
        f"Teks Saat Ini: \"{current_text_wm}\""
    )
    buttons = [
        [Button.inline(f"{'Nonaktifkan' if status_wm == 'AKTIF' else 'Aktifkan'} Watermark", b"toggle_watermark")],
        [Button.inline("Ganti Teks Watermark", b"set_watermark_text")],
        [Button.inline("Kembali ke Menu Utama", b"main_menu")]
    ]
    return text, buttons

# --- Fungsi Utilitas Klien Pengguna ---
async def ensure_connected(client, chat_id): 
    if not client: 
        logger.error(f"ensure_connected dipanggil dengan klien None untuk chat_id {chat_id}")
        return False
    try:
        if not client.is_connected():
            logger.info(f"Klien untuk {chat_id} tidak terhubung. Mencoba menghubungkan...")
            await client.connect()
            if not client.is_connected():
                 logger.error(f"Gagal menghubungkan klien untuk {chat_id} setelah memanggil connect().")
                 return False
            logger.info(f"Klien untuk {chat_id} berhasil terhubung.")
        return True
    except ConnectionError as e:
        logger.error(f"Gagal terhubung ke Telegram untuk {chat_id} (ConnectionError): {e}")
        return False
    except Exception as e:
        logger.error(f"Error tidak terduga saat memastikan koneksi klien untuk {chat_id}: {e}", exc_info=True)
        return False

async def validate_entity(user_client, entity_identifier_orig, chat_id, group_only=False):
    if not user_client:
        logger.error(f"validate_entity dipanggil dengan user_client None untuk {entity_identifier_orig}, chat {chat_id}")
        return (False, "Klien userbot tidak aktif.")

    validation_cache_key = f"validation_{str(entity_identifier_orig)}_{group_only}" 
    cached_result_tuple = entity_cache.get(validation_cache_key)
    if cached_result_tuple:
        cached_entity, timestamp = cached_result_tuple
        if time.time() - timestamp < CACHE_TTL:
            if group_only:
                is_valid_group = isinstance(cached_entity, Chat) or \
                                 (isinstance(cached_entity, Channel) and getattr(cached_entity, 'megagroup', False))
                if not is_valid_group: return (False, "Entitas yang di-cache bukan grup/supergrup.")
            logger.debug(f"Menggunakan hasil validasi cache untuk {entity_identifier_orig}")
            return (True, cached_entity) 
    
    error_message = f"Tidak bisa mendapatkan informasi untuk '{str(entity_identifier_orig)[:50]}'."
    entity_to_check = None
    
    processed_identifier = entity_identifier_orig
    if isinstance(entity_identifier_orig, str):
        if entity_identifier_orig.startswith('@'):
            pass 
        elif entity_identifier_orig.lstrip('-').isdigit():
            try: processed_identifier = int(entity_identifier_orig)
            except ValueError: pass
    
    try:
        await asyncio.sleep(0.1) 
        logger.debug(f"Validating entity: original='{entity_identifier_orig}', processed='{processed_identifier}' for chat_id={chat_id}")
        entity_to_check = await user_client.get_entity(processed_identifier)

        if not entity_to_check and isinstance(processed_identifier, int) and processed_identifier > 0:
            try_id_channel = int(f"-100{processed_identifier}")
            logger.debug(f"Validasi gagal untuk ID positif {processed_identifier}, mencoba lagi dengan {try_id_channel}")
            try:
                entity_to_check = await user_client.get_entity(try_id_channel)
            except ValueError: pass 
            except Exception: pass

        if entity_to_check:
            if len(entity_cache) >= ENTITY_CACHE_SIZE:
                try: entity_cache.popitem(last=False)
                except KeyError: pass
            entity_cache[validation_cache_key] = (entity_to_check, time.time())

            if group_only:
                is_valid_group = isinstance(entity_to_check, Chat) or \
                                 (isinstance(entity_to_check, Channel) and getattr(entity_to_check, 'megagroup', False))
                if not is_valid_group:
                    return (False, f"Entitas '{str(entity_identifier_orig)[:30]}' bukan grup atau supergrup publik.")
            return (True, entity_to_check)
        else:
            error_message = f"Entitas '{str(entity_identifier_orig)[:30]}' tidak ditemukan (get_entity mengembalikan None)."
            
    except ValueError as e_val: 
        error_message = f"Entitas '{str(entity_identifier_orig)[:30]}' tidak ditemukan atau format tidak valid: {e_val}"
    except TypeError as e_type: 
         error_message = f"Tipe input tidak valid untuk '{str(entity_identifier_orig)[:30]}': {e_type}"
    except FloodWaitError as e_flood:
        error_message = f"Kena FloodWait saat validasi '{str(entity_identifier_orig)[:30]}': {e_flood.seconds} detik. Coba beberapa saat lagi."
        logger.warning(f"FloodWait {e_flood.seconds}s validasi entitas {entity_identifier_orig} untuk {chat_id}.")
    except (UsernameNotOccupiedError, UsernameInvalidError):
        error_message = f"Username '{str(entity_identifier_orig)[:30]}' tidak ditemukan atau tidak valid."
    except ChannelPrivateError: error_message = f"Channel/Grup '{str(entity_identifier_orig)[:30]}' privat."
    except ChatAdminRequiredError: error_message = f"Memerlukan hak admin di '{str(entity_identifier_orig)[:30]}'."
    except RpcCallFailError as e_rpc: error_message = f"Gagal RPC Telegram untuk '{str(entity_identifier_orig)[:30]}': {e_rpc}"
    except UserChannelsTooMuchError: error_message = f"Pengguna telah bergabung terlalu banyak channel/grup."
    except Exception as e_gen:
        error_message = f"Error validasi tidak terduga untuk '{str(entity_identifier_orig)[:30]}': {type(e_gen).__name__}"
        logger.error(f"Error validasi entitas tidak terduga '{entity_identifier_orig}' untuk {chat_id}: {e_gen}", exc_info=True)
    
    logger.warning(f"Validasi gagal untuk '{entity_identifier_orig}' (Pengguna: {chat_id}): {error_message}")
    return (False, error_message)


async def verify_session(user_client, chat_id): 
    if not user_client: return False 
    try:
        if not await ensure_connected(user_client, chat_id):
             warning_counts[chat_id] += 1
             if warning_counts[chat_id] >= MAX_WARNINGS:
                await bot.send_message(chat_id, "Sesi Anda bermasalah (gagal konek terus-terusan). Sesi dihentikan. Silakan daftar ulang dengan /start.")
                await logout_user(chat_id, "CONNECTION_FAILED_MAX_ATTEMPTS")
                return False
             return False
        me = await user_client.get_me()
        if not me:
            warning_counts[chat_id] += 1
            if warning_counts[chat_id] >= MAX_WARNINGS:
                await bot.send_message(chat_id, "Sesi Anda terdeteksi bermasalah (get_me gagal). Sesi dihentikan. Silakan daftar ulang dengan /start.")
                await logout_user(chat_id, "GET_ME_FAILED")
                return False
            return False
        warning_counts[chat_id] = 0
        return True
    except (AuthKeyUnregisteredError, SessionRevokedError, UserDeactivatedBanError) as e:
        logger.error(f"Verifikasi sesi gagal untuk {chat_id} (fatal): {e}. Logout.")
        await bot.send_message(chat_id, f"Sesi Anda tidak valid atau telah dicabut: {type(e).__name__}. Sesi dihentikan. Silakan daftar ulang dengan /start.")
        await logout_user(chat_id, "FATAL_SESSION_ERROR")
        return False
    except Exception as e: 
        logger.error(f"Error tidak terduga saat verifikasi sesi untuk {chat_id}: {e}", exc_info=True)
        warning_counts[chat_id] += 1
    if warning_counts[chat_id] >= MAX_WARNINGS: await logout_user(chat_id, "MAX_WARNINGS_REACHED"); return False
    return False

async def logout_user(chat_id, reason="MANUAL_LOGOUT"):
    try:
        logger.info(f"Memulai proses logout untuk pengguna {chat_id}. Alasan: {reason}")
        client_to_logout = user_clients.pop(chat_id, None) 
        if client_to_logout and client_to_logout.is_connected():
            try: await client_to_logout.disconnect()
            except Exception as e_disc: logger.error(f"Error disconnect user client {chat_id} saat logout: {e_disc}")

        task_to_cancel = user_tasks.pop(chat_id, None) 
        if task_to_cancel and not task_to_cancel.done():
            task_to_cancel.cancel()
        
        _phone, _session, old_bot_data = await get_user_data(chat_id) 
        fresh_bot_data = copy.deepcopy(DEFAULT_BOT_DATA)
        fresh_bot_data['is_registered'] = False 
        fresh_bot_data['session_string'] = None 
        
        if reason != "KEY_EXPIRED":
            fresh_bot_data['active_key_value'] = old_bot_data.get('active_key_value')
            fresh_bot_data['active_key_type'] = old_bot_data.get('active_key_type')
            fresh_bot_data['key_expiry_timestamp'] = old_bot_data.get('key_expiry_timestamp')
            fresh_bot_data['assigned_basic_watermark_text'] = old_bot_data.get('assigned_basic_watermark_text')
            fresh_bot_data['has_valid_key'] = old_bot_data.get('has_valid_key', False) 
        else: 
            fresh_bot_data['has_valid_key'] = False

        await save_user_data(chat_id, phone_number=_phone, session_string=None, bot_data=fresh_bot_data)
        if chat_id in user_data_cache: del user_data_cache[chat_id]
        if chat_id in warning_counts: del warning_counts[chat_id]
        logger.info(f"Pengguna {chat_id} berhasil logout.")
        return True
    except Exception as e: logger.error(f"Error saat logout pengguna {chat_id}: {e}", exc_info=True); return False

async def login_user(event_or_chat_id, phone_number_ext=None):
    chat_id = event_or_chat_id.chat_id if hasattr(event_or_chat_id, 'chat_id') else event_or_chat_id
    phone_number_to_use = phone_number_ext
    if hasattr(event_or_chat_id, 'contact') and event_or_chat_id.contact:
        phone_number_to_use = event_or_chat_id.contact.phone_number
    
    if not phone_number_to_use:
        _db_phone, _, _ = await get_user_data(chat_id)
        phone_number_to_use = _db_phone

    if not phone_number_to_use:
        await bot.send_message(chat_id, "Gagal mendapatkan nomor telepon untuk login userbot.")
        return

    if not phone_number_to_use.startswith('+'): phone_number_to_use = '+' + phone_number_to_use

    _ph_login, session_string_login, bot_data_login = await get_user_data(chat_id)
    user_client = TelegramClient(StringSession(session_string_login or ""), API_ID, API_HASH, loop=loop)
    user_clients[chat_id] = user_client

    if not await ensure_connected(user_client, chat_id):
        await bot.send_message(chat_id, "Gagal menghubungkan klien pengguna.")
        if chat_id in user_clients: del user_clients[chat_id] 
        return

    is_authorized = await user_client.is_user_authorized()
    if not is_authorized:
        try:
            await user_client.send_code_request(phone_number_to_use)
            await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': 'phone_code_userbot'})
            await bot.send_message(chat_id, "Kode verifikasi userbot telah dikirim ke akun Telegram Anda. Silakan balas dengan kode (misal: 1 2 3 4 5).")
        except Exception as e:
            logger.error(f"Error mengirim kode userbot ke {chat_id} ({phone_number_to_use}): {e}", exc_info=True)
            await bot.send_message(chat_id, f"Gagal mengirim kode userbot: {e}.")
            if chat_id in user_clients: del user_clients[chat_id]
    else:
        new_session_string = user_client.session.save()
        bot_data_login_update = bot_data_login.copy()
        bot_data_login_update['is_registered'] = True
        bot_data_login_update['awaiting_input_type'] = None
        bot_data_login_update['awaiting_2fa'] = False
        await update_user_data_db(chat_id, phone_number=phone_number_to_use, session_string=new_session_string, bot_data_update=bot_data_login_update)
        
        status_text, buttons = main_menu(bot_data_login_update)
        await bot.send_message(chat_id, f"Berhasil masuk userbot dengan sesi yang sudah ada!\n\n{status_text}", buttons=buttons)
        await manage_forward_copy_task(chat_id, bot_data_login_update) # Panggil task manager baru

async def manage_forward_copy_task(chat_id, bot_data): 
    task_key = chat_id
    should_run = (bot_data.get('is_forwarding') or bot_data.get('is_copying')) and bot_data.get('is_registered') and bot_data.get('has_valid_key') and \
                 (bot_data.get('key_expiry_timestamp', 0) > time.time() or is_admin(chat_id)) 
    existing_task = user_tasks.get(task_key) 

    if existing_task and not existing_task.done():
        if not should_run:
            existing_task.cancel(); 
            if task_key in user_tasks: del user_tasks[task_key]
    elif should_run and (not existing_task or existing_task.done()):
        user_tasks[task_key] = asyncio.create_task(forward_and_copy_task(chat_id)) # Nama task baru

# --- Handler Bot Utama ---
@bot.on(events.NewMessage(pattern='/start'))
async def start(event):
    chat_id = event.chat_id
    _phone, _session, bot_data = await get_user_data(chat_id) 
    
    made_changes_schema = False
    temp_data_check = bot_data.copy()
    for key, default_value in DEFAULT_BOT_DATA.items():
        if key not in temp_data_check:
            temp_data_check[key] = copy.deepcopy(default_value); made_changes_schema = True
    keys_to_remove = [k for k in temp_data_check if k not in DEFAULT_BOT_DATA]
    if keys_to_remove:
        for k_rem in keys_to_remove: del temp_data_check[k_rem]; made_changes_schema = True

    if made_changes_schema:
        bot_data = temp_data_check
        await save_user_data(chat_id, phone_number=_phone, session_string=_session, bot_data=bot_data)
        _phone, _session, bot_data = await get_user_data(chat_id) 

    bot_data_update = {'awaiting_input_type': None, 'current_page_context': {}, 'admin_message_to_edit_id': None} 

    if is_admin(chat_id):
        bot_data_update['has_valid_key'] = True 
        bot_data_update['active_key_type'] = 'admin' 
        await update_user_data_db(chat_id, bot_data_update=bot_data_update)
        
        text_admin, buttons_admin = admin_main_menu()
        admin_panel_msg = await event.respond(f"Selamat datang, Admin!\n{text_admin}", buttons=buttons_admin)
        
        _a_phone, _a_session, admin_bot_data_start = await get_user_data(chat_id) 
        if not admin_bot_data_start.get('is_registered'):
             await bot.send_message(chat_id, 
                                    "Untuk menggunakan fitur userbot (seperti Copy, Tambah Grup), silakan setel userbot pribadi Anda.",
                                    buttons=[[Button.inline("✔️ Setel Userbot Admin Sekarang", "admin_setup_userbot_confirm")],
                                             [Button.inline("Lanjut ke Panel Admin Saja", f"admin_panel_ok:{admin_panel_msg.id if admin_panel_msg else 0}")]]
                                   ) 
        return

    user_has_valid_key = bot_data.get('has_valid_key', False)
    key_expiry = bot_data.get('key_expiry_timestamp')

    if user_has_valid_key and key_expiry and time.time() < key_expiry:
        if bot_data.get('is_registered') and _session: 
            status_text_main, buttons_main = main_menu(bot_data)
            await event.respond(f"Selamat datang kembali!\n\n{status_text_main}", buttons=buttons_main)
        else: 
            await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': 'phone_share_prompt'})
            await event.respond("Kunci Anda aktif! Silakan bagikan kontak Anda untuk mengaktifkan fitur userbot.",
                                buttons=[Button.request_phone("✔️ Bagikan Kontak untuk Login Userbot")])
    else:
        if key_expiry and time.time() >= key_expiry:
            await event.respond("Kunci Anda telah kedaluwarsa.")
            bot_data_update.update({
                'active_key_value': None, 'active_key_type': None, 
                'key_expiry_timestamp': None, 'has_valid_key': False,
                'assigned_basic_watermark_text': None, 'is_registered': False, 'session_string': None
            }) 
        
        bot_data_update['awaiting_input_type'] = None 
        await update_user_data_db(chat_id, bot_data_update=bot_data_update)
        
        prompt_text = "Selamat datang! Untuk menggunakan bot ini, Anda memerlukan kunci akses."
        prompt_buttons = [
            [Button.inline("🔑 Masukkan Kunci", b"prompt_enter_key")],
            [Button.url("FREE KEY", KEY_PURCHASE_CONTACT)]
        ]
        if WELCOME_IMAGE_URL:
            try: await event.respond(file=WELCOME_IMAGE_URL, message=prompt_text, buttons=prompt_buttons)
            except Exception as e_img: logger.error(f"Gagal mengirim gambar selamat datang kunci: {e_img}"); await event.respond(prompt_text, buttons=prompt_buttons)
        else: await event.respond(prompt_text, buttons=prompt_buttons)

@bot.on(events.NewMessage(func=lambda e: e.contact))
async def handle_contact(event):
    chat_id = event.chat_id
    _phone, _session, bot_data = await get_user_data(chat_id)

    if is_admin(chat_id) and bot_data.get('awaiting_input_type') == 'admin_userbot_setup_contact':
        await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': None})
        phone_number_admin = event.contact.phone_number
        if not phone_number_admin.startswith('+'): phone_number_admin = '+' + phone_number_admin
        await update_user_data_db(chat_id, phone_number=phone_number_admin)
        await login_user(event) 
        text_adm, btns_adm = admin_main_menu()
        await event.respond(f"Userbot admin telah disetel!\n{text_adm}", buttons=btns_adm)
        return

    if bot_data.get('has_valid_key') and bot_data.get('awaiting_input_type') == 'phone_share_prompt':
        await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': None})
        phone_number_user = event.contact.phone_number
        if not phone_number_user.startswith('+'): phone_number_user = '+' + phone_number_user
        await update_user_data_db(chat_id, phone_number=phone_number_user)
        await login_user(event) 
    else:
        await event.respond("Silakan aktifkan kunci dahulu sebelum membagikan kontak, atau pastikan Anda mengklik tombol yang benar.")

@bot.on(events.NewMessage())
async def handle_any_message(event):
    chat_id = event.chat_id
    text = event.message.text.strip() if event.message.text else ""

    if event.contact or (text and text.startswith('/start')): return 

    _phone, _session, bot_data = await get_user_data(chat_id)
    awaiting_type = bot_data.get('awaiting_input_type')
    admin_msg_id_to_edit = bot_data.get('admin_message_to_edit_id')

    if awaiting_type == 'enter_key_input' and text:
        try:
            async with db_pool.acquire() as conn:
                key_record = await conn.fetchrow("SELECT * FROM access_keys WHERE key_value = $1", text)
            
            if not key_record:
                await event.respond("Kunci tidak ditemukan. Silakan periksa kembali atau beli kunci baru."); return
            
            if key_record['is_claimed'] and key_record['claimed_by_chat_id'] != chat_id :
                await event.respond("Kunci ini telah digunakan oleh pengguna lain."); return
            
            key_generation_ts = key_record['generation_timestamp']
            key_duration_s = key_record['duration_seconds']
            key_inherent_expiry_ts = key_generation_ts + key_duration_s
            
            if time.time() > key_inherent_expiry_ts:
                await event.respond("Kunci ini telah kedaluwarsa (belum pernah diklaim tapi waktunya habis)."); return

            claim_ts = int(time.time())
            user_key_expiry_ts = claim_ts + key_record['duration_seconds']

            async with db_pool.acquire() as conn:
                async with conn.transaction():
                    locked_key_record = await conn.fetchrow("SELECT * FROM access_keys WHERE key_value = $1 FOR UPDATE", text)
                    if not locked_key_record or locked_key_record['is_claimed'] and locked_key_record['claimed_by_chat_id'] != chat_id :
                        await event.respond("Kunci ini baru saja digunakan atau tidak valid lagi. Coba kunci lain.")
                        return 

                    await conn.execute(
                        """
                        UPDATE access_keys 
                        SET is_claimed = TRUE, claimed_by_chat_id = $1, claim_timestamp = $2
                        WHERE key_value = $3
                        """, 
                        chat_id, claim_ts, text
                    )

            user_data_update = {
                'active_key_value': text,
                'active_key_type': key_record['key_type'],
                'key_expiry_timestamp': user_key_expiry_ts,
                'has_valid_key': True,
                'awaiting_input_type': 'phone_share_prompt', 
                'is_registered': False, 
                'session_string': None 
            }
            if key_record['key_type'] == 'basic':
                user_data_update['assigned_basic_watermark_text'] = key_record['assigned_watermark_text']
                user_data_update['watermark_enabled'] = True if key_record['assigned_watermark_text'] else False
                user_data_update['watermark_text'] = key_record['assigned_watermark_text'] or DEFAULT_GLOBAL_WATERMARK_TEXT 
            elif key_record['key_type'] == 'vip':
                user_data_update['watermark_text'] = bot_data.get('watermark_text', DEFAULT_GLOBAL_WATERMARK_TEXT)
                user_data_update['watermark_enabled'] = bot_data.get('watermark_enabled', False)

            await update_user_data_db(chat_id, bot_data_update=user_data_update)
            await event.respond(f"Kunci {key_record['key_type'].upper()} berhasil diaktifkan! 🎉\nKadaluwarsa pada: {datetime.datetime.fromtimestamp(user_key_expiry_ts).strftime('%Y-%m-%d %H:%M')}\n\nSilakan bagikan kontak Anda untuk melanjutkan.",
                                buttons=[Button.request_phone("✔️ Bagikan Kontak untuk Login Userbot")])
        except Exception as e_key_claim:
            logger.error(f"Error saat memproses klaim kunci {text} untuk {chat_id}: {e_key_claim}", exc_info=True)
            await event.respond("Terjadi kesalahan saat memproses kunci Anda. Coba lagi nanti.")
        return

    if bot_data.get('has_valid_key') or is_admin(chat_id):
        if awaiting_type == 'phone_code_userbot' and text and all(c.isdigit() or c.isspace() for c in text):
            if chat_id not in user_clients: await event.respond("Klien pengguna tidak ditemukan."); return
            user_client_code = user_clients[chat_id]
            _phone_db, _, bot_data_code = await get_user_data(chat_id) 
            code_input = "".join(text.split())
            try:
                phone_to_sign_in = _phone_db 
                if not phone_to_sign_in : 
                    await event.respond("Nomor telepon tidak ditemukan untuk sign in. Coba /start lagi.")
                    return

                await user_client_code.sign_in(phone=phone_to_sign_in, code=code_input)
                session_new_code = user_client_code.session.save()
                
                bot_data_update_login = bot_data_code.copy()
                bot_data_update_login['is_registered'] = True
                bot_data_update_login['awaiting_input_type'] = None
                bot_data_update_login['awaiting_2fa'] = False
                
                await update_user_data_db(chat_id, session_string=session_new_code, bot_data_update=bot_data_update_login)
                status_text_login, buttons_login = main_menu(bot_data_update_login)
                await event.respond(f"Login userbot berhasil!\n\n{status_text_login}", buttons=buttons_login)
                await manage_forward_copy_task(chat_id, bot_data_update_login)

            except PhoneCodeInvalidError: await event.respond("Kode verifikasi userbot tidak valid.")
            except SessionPasswordNeededError:
                await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': '2fa_password_userbot', 'awaiting_2fa': True}) 
                await event.respond("Akun userbot Anda memiliki 2FA. Masukkan kata sandi 2FA:")
            except Exception as e: await event.respond(f"Gagal login userbot: {e}."); logger.error(f"Login userbot error: {e}", exc_info=True)
            return

        elif awaiting_type == '2fa_password_userbot' and bot_data.get('awaiting_2fa'): 
            if chat_id not in user_clients: await event.respond("Klien pengguna tidak ditemukan."); return
            user_client_2fa = user_clients[chat_id]
            password_2fa = text
            try:
                await user_client_2fa.sign_in(password=password_2fa)
                session_2fa_new = user_client_2fa.session.save()
                _ph_2fa, _ss_2fa, bot_data_2fa = await get_user_data(chat_id)

                bot_data_update_2fa = bot_data_2fa.copy()
                bot_data_update_2fa['is_registered'] = True
                bot_data_update_2fa['awaiting_input_type'] = None
                bot_data_update_2fa['awaiting_2fa'] = False
                await update_user_data_db(chat_id, session_string=session_2fa_new, bot_data_update=bot_data_update_2fa)
                status_text_2fa, buttons_2fa = main_menu(bot_data_update_2fa)
                await event.respond(f"Login userbot 2FA berhasil!\n\n{status_text_2fa}", buttons=buttons_2fa)
                await manage_forward_copy_task(chat_id, bot_data_update_2fa)
            except Exception as e: await event.respond(f"Gagal login userbot 2FA: {e}."); logger.error(f"Login 2FA userbot error: {e}", exc_info=True)
            return
        
        # Penanganan untuk durasi mode
        elif awaiting_type == 'awaiting_forward_duration' and text:
            duration_s = parse_duration_to_seconds(text) if text.lower() not in ['skip', 'selamanya'] else None
            expiry_ts = (int(time.time()) + duration_s) if duration_s else None
            await update_user_data_db(chat_id, bot_data_update={'is_forwarding': True, 'forward_expiry_timestamp': expiry_ts, 'awaiting_input_type': None})
            await event.respond(f"Mode Forward diaktifkan {'selama ' + text if expiry_ts else 'selamanya'}.")
            bd_upd = await get_user_data(chat_id)
            await manage_forward_copy_task(chat_id, bd_upd[2])
            return

        elif awaiting_type == 'awaiting_copy_duration' and text:
            duration_s = parse_duration_to_seconds(text) if text.lower() not in ['skip', 'selamanya'] else None
            expiry_ts = (int(time.time()) + duration_s) if duration_s else None
            await update_user_data_db(chat_id, bot_data_update={'is_copying': True, 'copy_expiry_timestamp': expiry_ts, 'awaiting_input_type': None})
            await event.respond(f"Mode Copy diaktifkan {'selama ' + text if expiry_ts else 'selamanya'}.")
            bd_upd = await get_user_data(chat_id)
            await manage_forward_copy_task(chat_id, bd_upd[2])
            return

        # Penanganan untuk link
        elif awaiting_type == 'awaiting_single_link' and text:
            _p, _s, bd_link = await get_user_data(chat_id)
            fwd_sets = bd_link.get('forward_sets', [])
            fwd_sets.append({'type': 'single', 'link': text, 'id': str(uuid4())})
            await update_user_data_db(chat_id, bot_data_update={'forward_sets': fwd_sets, 'awaiting_input_type': None})
            await event.respond("Link single berhasil disimpan!")
            return

        elif awaiting_type == 'awaiting_dual_link_1' and text:
            temp_data = {'link1': text}
            await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': 'awaiting_dual_link_delay', 'temp_dual_link_data': temp_data})
            await event.respond("Link pertama disimpan. Sekarang masukkan delay (jeda) dalam detik:")
            return
        
        elif awaiting_type == 'awaiting_dual_link_delay' and text.isdigit():
            temp_data = bot_data.get('temp_dual_link_data', {})
            if not temp_data.get('link1'):
                await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': None, 'temp_dual_link_data': {}})
                await event.respond("Error: Link pertama tidak ditemukan. Ulangi proses."); return
            temp_data['delay'] = int(text)
            await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': 'awaiting_dual_link_2', 'temp_dual_link_data': temp_data})
            await event.respond("Delay disimpan. Sekarang kirim link kedua:")
            return
        
        elif awaiting_type == 'awaiting_dual_link_2' and text:
            temp_data = bot_data.get('temp_dual_link_data', {})
            if not temp_data.get('link1') or 'delay' not in temp_data:
                await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': None, 'temp_dual_link_data': {}})
                await event.respond("Error: Data link atau delay tidak lengkap. Ulangi proses."); return
            temp_data['link2'] = text
            temp_data['type'] = 'dual'
            temp_data['id'] = str(uuid4())
            
            _p, _s, bd_link2 = await get_user_data(chat_id)
            fwd_sets = bd_link2.get('forward_sets', [])
            fwd_sets.append(temp_data)
            await update_user_data_db(chat_id, bot_data_update={'forward_sets': fwd_sets, 'awaiting_input_type': None, 'temp_dual_link_data': {}})
            await event.respond("Set link ganda (dual link) berhasil disimpan!")
            return


        if bot_data.get('is_registered') or is_admin(chat_id): 
            if awaiting_type == 'set_delay' and text and text.isdigit():
                delay_val_input = int(text)
                if delay_val_input <= 0: await event.respond("Delay harus angka positif."); return
                await update_user_data_db(chat_id, bot_data_update={'delay': delay_val_input, 'awaiting_input_type': None})
                _p, _s, bd_upd = await get_user_data(chat_id); st, btns = main_menu(bd_upd); 
                msg_id_delay = bot_data.get('admin_message_to_edit_id') 
                response_text_delay = f"Delay global diatur ke {bd_upd.get('delay')} detik!\n\n{st}"
                try:
                    if msg_id_delay: await bot.edit_message(chat_id, msg_id_delay, response_text_delay, buttons=btns)
                    else: await event.respond(response_text_delay, buttons=btns) 
                except Exception as e_edit_delay: logger.error(f"Gagal edit/respond pesan delay: {e_edit_delay}"); await event.respond(response_text_delay, buttons=btns) 
                await update_user_data_db(chat_id, bot_data_update={'admin_message_to_edit_id': None})
                return

            elif awaiting_type == 'save_text_media':
                _p, _s, bd_stm = await get_user_data(chat_id)
                saved_texts_list = bd_stm.get('saved_texts', [])
                current_text_to_save = event.message.text 
                current_media_id_to_save = None; current_media_type_to_save = None
                if event.message.media:
                    if hasattr(event.message.media, 'photo'): current_media_id_to_save = event.message.media.photo.id; current_media_type_to_save = 'photo'
                    elif hasattr(event.message.media, 'document'): current_media_id_to_save = event.message.media.document.id; current_media_type_to_save = 'document'
                    elif hasattr(event.message.media, 'video'): current_media_id_to_save = event.message.media.video.id; current_media_type_to_save = 'video'
                
                is_duplicate_stm = any(
                    item.get('text') == current_text_to_save and item.get('media_file_id') == current_media_id_to_save 
                    for item in saved_texts_list
                )
                if not current_text_to_save and not event.message.media: await event.respond("Tidak ada yang disimpan."); return
                if not is_duplicate_stm:
                    new_item_stm = {'id': str(uuid4()), 'text': current_text_to_save, 'entities': [entity_to_dict(e) for e in event.message.entities or []], 'media_file_id': current_media_id_to_save, 'media_file_type': current_media_type_to_save, 'timestamp': time.time()}
                    saved_texts_list.append(new_item_stm)
                    await update_user_data_db(chat_id, bot_data_update={'saved_texts': saved_texts_list, 'awaiting_input_type': None})
                    _p2, _s2, bd_menu = await get_user_data(chat_id); st_menu, _ = main_menu(bd_menu);
                    btns_confirm = [[Button.inline("Tes Kirim ke Disimpan", f"send_to_me_{new_item_stm['id']}")], [Button.inline("Kembali", b"main_menu")]]
                    
                    msg_id_save_media = bot_data.get('admin_message_to_edit_id')
                    response_text_save_media = f"Konten disimpan!\n\n{st_menu}"
                    try:
                        if msg_id_save_media: await bot.edit_message(chat_id, msg_id_save_media, response_text_save_media, buttons=btns_confirm)
                        else: await event.respond(response_text_save_media, buttons=btns_confirm)
                    except Exception as e_edit_save_media : logger.error(f"Gagal edit/respond save_text_media: {e_edit_save_media}"); await event.respond(response_text_save_media, buttons=btns_confirm)
                    await update_user_data_db(chat_id, bot_data_update={'admin_message_to_edit_id': None})

                else: await event.respond("Konten ini sudah ada."); return

            elif awaiting_type == 'add_group_manual' and text:
                group_identifier_input = text.strip() 
                
                client_for_add_group = user_clients.get(chat_id)
                if not client_for_add_group and is_admin(chat_id) and bot_data.get('is_registered') and bot_data.get('session_string'):
                    client_for_add_group = TelegramClient(StringSession(bot_data.get('session_string')), API_ID, API_HASH, loop=loop)
                    if not await client_for_add_group.connect(): 
                        await event.respond("Gagal menghubungkan userbot admin untuk menambah grup."); return
                elif not client_for_add_group or not await client_for_add_group.is_user_authorized():
                    await event.respond("Klien pengguna belum login/aktif (untuk menambah grup)."); return

                user_client_grp = client_for_add_group
                msg_id_add_group_flow = bot_data.get('admin_message_to_edit_id') 
                
                entity_to_process = group_identifier_input
                if "t.me/joinchat/" in group_identifier_input or "t.me/+" in group_identifier_input:
                    try:
                        invite_hash = group_identifier_input.split('/')[-1].split('?')[0]
                        logger.info(f"Mencoba bergabung via invite_hash: {invite_hash}")
                        updates_grp = await user_client_grp(functions.messages.ImportChatInviteRequest(hash=invite_hash))
                        if updates_grp.chats:
                            entity_to_process = updates_grp.chats[0] 
                            await event.respond(f"Berhasil bergabung ke: {getattr(entity_to_process, 'title', 'Tanpa Judul')}.")
                        else: 
                            await event.respond("Gagal memproses link undangan setelah mencoba bergabung."); return
                    except Exception as e_join: 
                        await event.respond(f"Gagal bergabung melalui link: {e_join}"); return
                
                is_valid_grp, resolved_entity_or_error = await validate_entity(user_client_grp, entity_to_process, chat_id, group_only=True)
                
                if is_valid_grp and resolved_entity_or_error: 
                    resolved_entity_obj_final = resolved_entity_or_error 
                    _p, _s, bd_grp = await get_user_data(chat_id); target_groups_list = bd_grp.get('target_groups', [])
                    id_to_store_grp = str(get_peer_id(resolved_entity_obj_final)) 
                    
                    is_duplicate_strong = False
                    for existing_target_str in target_groups_list:
                        try:
                            existing_peer_id_int = int(existing_target_str) 
                            if existing_peer_id_int == get_peer_id(resolved_entity_obj_final): 
                                is_duplicate_strong = True; break
                        except ValueError: 
                             if existing_target_str == id_to_store_grp or (hasattr(resolved_entity_obj_final, 'username') and existing_target_str == f"@{resolved_entity_obj_final.username}"):
                                is_duplicate_strong = True; break
                        except Exception: continue
                    
                    if not is_duplicate_strong:
                        target_groups_list.append(id_to_store_grp) 
                        await update_user_data_db(chat_id, bot_data_update={'target_groups': target_groups_list, 'awaiting_input_type': None})
                        _p2, _s2, bd_menu = await get_user_data(chat_id); st_menu, btns_menu = main_menu(bd_menu);
                        
                        response_text_add_group = f"Grup '{getattr(resolved_entity_obj_final, 'title', id_to_store_grp)}' (ID: {id_to_store_grp}) ditambahkan!\n\n{st_menu}"
                        try:
                            if msg_id_add_group_flow: await bot.edit_message(chat_id, msg_id_add_group_flow, response_text_add_group, buttons=btns_menu)
                            else: await event.respond(response_text_add_group, buttons=btns_menu)
                        except Exception as e_edit_add_group: logger.error(f"Gagal edit/respond add_group: {e_edit_add_group}"); await event.respond(response_text_add_group, buttons=btns_menu)
                        await update_user_data_db(chat_id, bot_data_update={'admin_message_to_edit_id': None})
                    else: await event.respond(f"Grup '{getattr(resolved_entity_obj_final, 'title', id_to_store_grp)}' (ID: {id_to_store_grp}) sudah ada.")
                else: 
                    await event.respond(f"Entitas {group_identifier_input} tidak valid: {resolved_entity_or_error}"); return
                
                if is_admin(chat_id) and client_for_add_group and chat_id not in user_clients and client_for_add_group.is_connected():
                    await client_for_add_group.disconnect()

            elif awaiting_type == 'set_watermark_text_input' and text and bot_data.get('active_key_type') == 'vip':
                if not text.strip(): await event.respond("Teks watermark tidak boleh kosong."); return
                await update_user_data_db(chat_id, bot_data_update={'watermark_text': text.strip(), 'awaiting_input_type': None})
                _p, _s, bd_upd = await get_user_data(chat_id); txt_menu, btns_menu = watermark_settings_menu(bd_upd);
                
                msg_id_wm_vip = bot_data.get('admin_message_to_edit_id')
                response_text_wm_vip = f"Teks watermark diubah!\n\n{txt_menu}"
                try:
                    if msg_id_wm_vip: await bot.edit_message(chat_id, msg_id_wm_vip, response_text_wm_vip, buttons=btns_menu)
                    else: await event.respond(response_text_wm_vip, buttons=btns_menu)
                except Exception as e_edit_wm_vip: logger.error(f"Gagal edit/respond set watermark vip: {e_edit_wm_vip}"); await event.respond(response_text_wm_vip, buttons=btns_menu)
                await update_user_data_db(chat_id, bot_data_update={'admin_message_to_edit_id': None})
                return
    
    if is_admin(chat_id):
        if awaiting_type == 'admin_broadcast_message' and text:
            await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': None})
            await event.respond("Memulai proses broadcast...")
            sent_count, failed_count = 0, 0
            async with db_pool.acquire() as conn_bc:
                all_users_for_bc = await conn_bc.fetch("SELECT chat_id, bot_data FROM users") 
            for user_row in all_users_for_bc:
                target_user_id = user_row['chat_id']
                target_bot_data = json.loads(user_row['bot_data']) if user_row['bot_data'] else {}
                if target_bot_data.get('has_valid_key') and (not target_bot_data.get('key_expiry_timestamp') or time.time() < target_bot_data.get('key_expiry_timestamp', 0)):
                    try: await bot.send_message(target_user_id, text); sent_count += 1; await asyncio.sleep(0.1)
                    except Exception: failed_count +=1
            
            msg_id_bc = bot_data.get('admin_message_to_edit_id')
            response_text_bc = f"Broadcast selesai. Terkirim: {sent_count}, Gagal: {failed_count}."
            _t_bc, btns_bc_panel = admin_main_menu()
            try:
                if msg_id_bc: await bot.edit_message(chat_id, msg_id_bc, response_text_bc, buttons=btns_bc_panel) 
                else: await event.respond(response_text_bc, buttons=btns_bc_panel)
            except Exception as e_edit_bc: logger.error(f"Gagal edit/respond broadcast: {e_edit_bc}"); await event.respond(response_text_bc, buttons=btns_bc_panel)
            await update_user_data_db(chat_id, bot_data_update={'admin_message_to_edit_id': None})
            return
        
        elif awaiting_type == 'admin_generate_key_duration' and text:
            key_type_to_gen = bot_data.get('admin_temp_key_type')
            if not key_type_to_gen: 
                await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': None, 'admin_temp_key_type': None, 'admin_temp_key_duration_s': None, 'admin_message_to_edit_id': None}) 
                await event.respond("Error: Tipe kunci tidak ditemukan. Ulangi dari menu admin."); return
            
            duration_s = parse_duration_to_seconds(text)
            if duration_s is None: await event.respond("Format durasi tidak valid (contoh: 7d, 12h, 30m). Coba lagi:"); return

            if key_type_to_gen == 'basic':
                await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': 'admin_generate_basic_key_watermark', 'admin_temp_key_duration_s': duration_s}) 
                if admin_msg_id_to_edit:
                    try: await bot.edit_message(chat_id, admin_msg_id_to_edit, "Masukkan teks watermark untuk kunci Basic ini (opsional, kirim 'skip' jika tidak ada):")
                    except Exception as e_edit: logger.error(f"Gagal edit pesan admin watermark: {e_edit}"); await event.respond("Gagal lanjut, coba lagi.")
                else: await event.respond("Masukkan teks watermark untuk kunci Basic ini (opsional, kirim 'skip' jika tidak ada):")

            elif key_type_to_gen == 'vip':
                new_key_val = generate_unique_key("VIP-")
                generation_ts = int(time.time())
                original_expiry = generation_ts + duration_s 
                
                async with db_pool.acquire() as conn:
                    await conn.execute(
                        """INSERT INTO access_keys (key_value, key_type, duration_seconds, generated_by_admin_id, generation_timestamp, original_expiry_timestamp)
                           VALUES ($1, 'vip', $2, $3, $4, $5)""",
                        new_key_val, duration_s, chat_id, generation_ts, original_expiry
                    )
                await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': None, 'admin_temp_key_type': None, 'admin_temp_key_duration_s': None, 'admin_message_to_edit_id': None})
                _t_km_vip,btns_km_vip = admin_manage_keys_menu() 
                msg_content_vip = f"Kunci VIP baru digenerate:\n`{new_key_val}`\nDurasi: {text.strip()}" 
                if admin_msg_id_to_edit:
                    try: await bot.edit_message(chat_id, admin_msg_id_to_edit, msg_content_vip, buttons=btns_km_vip, parse_mode='md')
                    except Exception as e_edit: logger.error(f"Gagal edit pesan admin VIP key: {e_edit}"); await event.respond(msg_content_vip, buttons=btns_km_vip, parse_mode='md')
                else: await event.respond(msg_content_vip, buttons=btns_km_vip, parse_mode='md')
            return

        elif awaiting_type == 'admin_generate_basic_key_watermark' and text:
            key_duration_s = bot_data.get('admin_temp_key_duration_s')
            key_type_to_gen = bot_data.get('admin_temp_key_type') 
            if not key_duration_s or key_type_to_gen != 'basic': 
                await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': None, 'admin_temp_key_type': None, 'admin_temp_key_duration_s': None, 'admin_message_to_edit_id': None})
                await event.respond("Error: Durasi atau tipe kunci tidak ditemukan. Ulangi."); return
            
            assigned_wm_text = None
            if text.lower() != 'skip':
                assigned_wm_text = text.strip()

            new_key_val = generate_unique_key("BSC-")
            generation_ts = int(time.time())
            original_expiry = generation_ts + key_duration_s

            async with db_pool.acquire() as conn:
                await conn.execute(
                    """INSERT INTO access_keys (key_value, key_type, duration_seconds, generated_by_admin_id, generation_timestamp, original_expiry_timestamp, assigned_watermark_text)
                       VALUES ($1, 'basic', $2, $3, $4, $5, $6)""",
                    new_key_val, key_duration_s, chat_id, generation_ts, original_expiry, assigned_wm_text
                )
            await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': None, 'admin_temp_key_type': None, 'admin_temp_key_duration_s': None, 'admin_message_to_edit_id': None})
            wm_info = f"Watermark: {assigned_wm_text}" if assigned_wm_text else "Watermark: (Default Global)"
            dur_text = f"{key_duration_s // 86400}d" if key_duration_s % 86400 == 0 and key_duration_s >= 86400 else f"{key_duration_s // 3600}h" if key_duration_s % 3600 == 0 and key_duration_s >= 3600 else f"{key_duration_s // 60}m"
            _t_km_basic,btns_km_basic = admin_manage_keys_menu()
            msg_content_basic = f"Kunci Basic baru digenerate:\n`{new_key_val}`\nDurasi: {dur_text}\n{wm_info}" 
            if admin_msg_id_to_edit:
                try: await bot.edit_message(chat_id, admin_msg_id_to_edit, msg_content_basic, buttons=btns_km_basic, parse_mode='md')
                except Exception as e_edit: logger.error(f"Gagal edit pesan admin Basic key: {e_edit}"); await event.respond(msg_content_basic, buttons=btns_km_basic, parse_mode='md')
            else: await event.respond(msg_content_basic, buttons=btns_km_basic, parse_mode='md')
            return
        
        elif awaiting_type == 'admin_revoke_key_value_input' and text:
            key_to_revoke = text.strip()
            msg_to_edit_revoke = bot_data.get('admin_message_to_edit_id')
            try:
                async with db_pool.acquire() as conn:
                    key_record = await conn.fetchrow("SELECT * FROM access_keys WHERE key_value = $1", key_to_revoke)
                    _t_km_revoke,btns_km_revoke = admin_manage_keys_menu() 

                    if not key_record:
                        err_msg_revoke = f"Kunci `{key_to_revoke}` tidak ditemukan."
                        if msg_to_edit_revoke: await bot.edit_message(chat_id, msg_to_edit_revoke, err_msg_revoke, buttons=btns_km_revoke, parse_mode='md')
                        else: await event.respond(err_msg_revoke, buttons=btns_km_revoke, parse_mode='md')
                        return

                    claimed_by = key_record['claimed_by_chat_id']
                    
                    await conn.execute("DELETE FROM access_keys WHERE key_value = $1", key_to_revoke)
                    
                    if claimed_by:
                        _uphone, _usession, user_bot_data_revoke = await get_user_data(claimed_by)
                        user_bot_data_revoke_update = {
                            'active_key_value': None, 'active_key_type': None,
                            'key_expiry_timestamp': None, 'has_valid_key': False,
                            'assigned_basic_watermark_text': None,
                            'is_registered': False, 
                            'session_string': None
                        }
                        await update_user_data_db(claimed_by, bot_data_update=user_bot_data_revoke_update)
                        
                        client_to_logout_revoked = user_clients.pop(claimed_by, None)
                        if client_to_logout_revoked and client_to_logout_revoked.is_connected():
                            try: await client_to_logout_revoked.disconnect()
                            except Exception as e_disc_revoke: logger.error(f"Gagal disconnect klien {claimed_by} saat cabut kunci: {e_disc_revoke}")
                        
                        task_to_cancel_revoked = user_tasks.pop(claimed_by, None)
                        if task_to_cancel_revoked and not task_to_cancel_revoked.done():
                            task_to_cancel_revoked.cancel()
                        
                        try: await bot.send_message(claimed_by, f"Kunci akses Anda (`{key_to_revoke}`) telah dicabut oleh Admin. Akses Anda ke fitur bot telah dinonaktifkan. Silakan hubungi admin untuk informasi lebih lanjut atau untuk mendapatkan kunci baru.")
                        except Exception as e_notify_revoke: logger.warning(f"Gagal mengirim notifikasi cabut kunci ke {claimed_by}: {e_notify_revoke}")
                    
                    await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': None, 'admin_message_to_edit_id': None})
                    success_msg_revoke = f"Kunci `{key_to_revoke}` berhasil dicabut/dihapus."
                    if msg_to_edit_revoke: await bot.edit_message(chat_id, msg_to_edit_revoke, success_msg_revoke, buttons=btns_km_revoke, parse_mode='md')
                    else: await event.respond(success_msg_revoke, buttons=btns_km_revoke, parse_mode='md')

            except Exception as e_revoke:
                logger.error(f"Error saat mencabut kunci {key_to_revoke}: {e_revoke}", exc_info=True)
                _t_km_revoke_fail,btns_km_revoke_fail = admin_manage_keys_menu()
                fail_msg_revoke = f"Gagal mencabut kunci."
                if bot_data.get('admin_message_to_edit_id'): await bot.edit_message(chat_id, bot_data.get('admin_message_to_edit_id'), fail_msg_revoke, buttons=btns_km_revoke_fail)
                else: await event.respond(fail_msg_revoke, buttons=btns_km_revoke_fail)
            finally: 
                await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': None, 'admin_message_to_edit_id': None})
            return

@bot.on(events.CallbackQuery)
async def callback(event):
    chat_id = event.chat_id
    data = event.data.decode()
    logger.info(f"Callback diterima oleh {chat_id}: {data}")
    message_id_cb = event.message_id 

    _phone, _session, bot_data_cb = await get_user_data(chat_id) 

    if data in ["main_menu", "admin_panel", "admin_manage_keys"]:
        await update_user_data_db(chat_id, bot_data_update={
            'awaiting_input_type': None, 
            'admin_temp_key_type': None, 
            'admin_temp_key_duration_s': None,
            'admin_message_to_edit_id': None, 
            'current_page_context': {},
            'temp_dual_link_data': {}, # Reset data dual link juga
        })
        bot_data_cb = (await get_user_data(chat_id))[2] 

    if not is_admin(chat_id):
        if data == "prompt_enter_key":
            await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': 'enter_key_input'})
            try: await event.edit("Silakan masukkan kunci akses Anda:")
            except MessageNotModifiedError: await event.answer() 
            except Exception as e: logger.error(f"Error edit ke enter_key_input: {e}"); await event.answer()
            return
    
    if bot_data_cb.get('has_valid_key') or is_admin(chat_id): 
        if data == "main_menu":
            st_mm, btns_mm = main_menu(bot_data_cb)
            try: await event.edit(f"Menu Utama\n\n{st_mm}", buttons=btns_mm)
            except MessageNotModifiedError: pass; await event.answer()
            except Exception as e: logger.error(f"Error main_menu edit: {e}"); await event.answer("Gagal menampilkan menu.")
            return
        elif data.startswith("admin_panel_ok"): 
            try:
                if ':' in data:
                    try:
                        original_panel_msg_id = int(data.split(':')[1])
                        if original_panel_msg_id != 0 : await bot.delete_messages(chat_id, original_panel_msg_id)
                    except Exception as e_del_ok: logger.warning(f"Gagal menghapus pesan admin panel OK: {e_del_ok}")
                await event.delete() 
            except Exception: pass 
            
            txt_adm_ok, btns_adm_ok = admin_main_menu()
            await bot.send_message(chat_id, txt_adm_ok, buttons=btns_adm_ok) 
            return
        
        elif data == "forward_copy_menu":
            txt,btns = forward_copy_menu(bot_data_cb)
            try: await event.edit(f"Pengaturan Forward & Copy\n\n{txt}", buttons=btns)
            except MessageNotModifiedError:pass; await event.answer()
            except Exception as e: logger.error(f"Error forward_copy_menu edit: {e}"); await event.answer("Gagal menampilkan menu.")
            return

        elif data == "forward_on":
            if not bot_data_cb.get('forward_sets'): await event.answer("Tidak ada link forward yang disimpan!", alert=True); return
            await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': 'awaiting_forward_duration'})
            await event.edit("Masukkan durasi untuk mode Forward (contoh: 1h, 30m, 2d). Kirim 'skip' atau 'selamanya' untuk berjalan terus.", buttons=[[Button.inline("Batal", "forward_copy_menu")]])
            return

        elif data == "forward_off":
            await update_user_data_db(chat_id, bot_data_update={'is_forwarding': False, 'forward_expiry_timestamp': None})
            await event.answer("Mode Forward dinonaktifkan.")
            _p, _s, bd_upd = await get_user_data(chat_id); await manage_forward_copy_task(chat_id, bd_upd)
            txt, btns = forward_copy_menu(bd_upd)
            try: await event.edit(f"Pengaturan Forward & Copy\n\n{txt}", buttons=btns)
            except MessageNotModifiedError: pass
            return

        elif data == "copy_on": 
            if not bot_data_cb.get('is_registered') and not is_admin(chat_id): await event.answer("Login userbot dahulu!", alert=True); return
            client_for_copy_on = user_clients.get(chat_id)
            if not client_for_copy_on and is_admin(chat_id) and bot_data_cb.get('is_registered') and bot_data_cb.get('session_string'):
                client_for_copy_on = TelegramClient(StringSession(bot_data_cb.get('session_string')), API_ID, API_HASH, loop=loop)
                if not await client_for_copy_on.connect(): await event.answer("Gagal menghubungkan userbot admin!", alert=True); return
                user_clients[chat_id] = client_for_copy_on
            elif not client_for_copy_on : await event.answer("Klien userbot tidak aktif!", alert=True); return
            if not bot_data_cb.get('saved_texts') or not bot_data_cb.get('target_groups'): await event.answer("Simpan teks/media dan grup target dahulu!", alert=True); return
            
            await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': 'awaiting_copy_duration'})
            await event.edit("Masukkan durasi untuk mode Copy (contoh: 1h, 30m, 2d). Kirim 'skip' atau 'selamanya' untuk berjalan terus.", buttons=[[Button.inline("Batal", "forward_copy_menu")]])
            return
            
        elif data == "copy_off": 
            await update_user_data_db(chat_id, bot_data_update={'is_copying': False, 'copy_expiry_timestamp': None})
            await event.answer("Mode Copy dinonaktifkan.")
            _p, _s, bd_upd_off = await get_user_data(chat_id); await manage_forward_copy_task(chat_id, bd_upd_off)
            txt_off,btns_off = forward_copy_menu(bd_upd_off); 
            try: await event.edit(f"Pengaturan Forward & Copy\n\n{txt_off}", buttons=btns_off)
            except MessageNotModifiedError:pass
            return
            
        elif data == "save_link":
            btns_save_link_type = [
                [Button.inline("🔗 Single Link", b"save_single_link")],
                [Button.inline("🔗🔗 Dual Link", b"save_dual_link_1_prompt")],
                [Button.inline("Kembali", b"main_menu")]
            ]
            await event.edit("Pilih tipe link forward yang ingin disimpan:", buttons=btns_save_link_type)
            return

        elif data == "save_single_link":
            await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': 'awaiting_single_link'})
            await event.edit("Silakan kirim satu link pesan Telegram untuk disimpan.")
            return

        elif data == "save_dual_link_1_prompt":
            await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': 'awaiting_dual_link_1'})
            await event.edit("Mode Dual Link: Silakan kirim link pesan PERTAMA.")
            return

        elif data == "delete_link":
            await display_paginated_list(event, chat_id, bot_data_cb, 'forward_sets', 0, 'main_menu', edit_mode=True)
            return

        elif data == "set_delay": 
            await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': 'set_delay', 'admin_message_to_edit_id': message_id_cb})
            try: await event.edit("Masukkan delay global dalam detik:")
            except MessageNotModifiedError:pass; await event.answer()
            except Exception as e: logger.error(f"Error set_delay edit: {e}")
            return
        elif data == "save_text_media": 
            await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': 'save_text_media', 'admin_message_to_edit_id': message_id_cb})
            try: await event.edit("Kirim teks atau media untuk disimpan:")
            except MessageNotModifiedError:pass; await event.answer()
            except Exception as e: logger.error(f"Error save_text_media edit: {e}")
            return
        elif data == "delete_text_media": 
            await display_paginated_list(event, chat_id, bot_data_cb, 'saved_texts', 0, 'main_menu', edit_mode=True); return
        elif data == "add_group": 
            btns_ag = [[Button.inline("Manual", b"add_group_manual")], [Button.inline("Semua Grup Saya", b"add_all_my_groups")], [Button.inline("Kembali", b"main_menu")]]; 
            try: await event.edit("Pilih cara menambah:", buttons=btns_ag)
            except MessageNotModifiedError:pass; await event.answer()
            except Exception as e: logger.error(f"Error add_group edit: {e}")
            return
        elif data == "add_group_manual": 
            await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': 'add_group_manual', 'admin_message_to_edit_id': message_id_cb}); 
            try: await event.edit("Masukkan username/ID/link grup:")
            except MessageNotModifiedError:pass; await event.answer()
            except Exception as e: logger.error(f"Error add_group_manual edit: {e}")
            return
        elif data == "add_all_my_groups": 
            client_for_aamg = user_clients.get(chat_id)
            if not client_for_aamg and is_admin(chat_id) and bot_data_cb.get('is_registered') and bot_data_cb.get('session_string'):
                 client_for_aamg = TelegramClient(StringSession(bot_data_cb.get('session_string')), API_ID, API_HASH, loop=loop)
                 if not await client_for_aamg.connect(): await event.answer("Gagal menghubungkan userbot admin!", alert=True); return
            elif not client_for_aamg or not await client_for_aamg.is_user_authorized() : await event.answer("Klien userbot tidak aktif!",True); return
            
            await event.answer("Memproses..."); 
            user_client_aamg = client_for_aamg
            current_targets = bot_data_cb.get('target_groups',[]); added=0;
            async for d in user_client_aamg.iter_dialogs():
                if d.is_group:
                    try: 
                        entity_aamg = await user_client_aamg.get_entity(d.id)
                        eid = str(get_peer_id(entity_aamg)) 
                    except: continue 
                    if eid not in current_targets: current_targets.append(eid); added+=1
            if added > 0: await update_user_data_db(chat_id, bot_data_update={'target_groups': current_targets})
            try: await event.edit(f"{added} grup baru ditambahkan. Total: {len(current_targets)}", buttons=[[Button.inline("Kembali",b"main_menu")]])
            except MessageNotModifiedError:pass; await event.answer()
            except Exception as e: logger.error(f"Error add_all_my_groups edit: {e}")
            finally: 
                if is_admin(chat_id) and client_for_aamg and chat_id not in user_clients and client_for_aamg.is_connected():
                    await client_for_aamg.disconnect()
            return
        elif data == "delete_group": 
            await display_paginated_list(event, chat_id, bot_data_cb, 'target_groups', 0, 'main_menu', edit_mode=True); return
        elif data == "delete_all_target_groups": 
            await update_user_data_db(chat_id, bot_data_update={'target_groups':[]}); await event.answer("Semua grup target dihapus.")
            _p, _s, bd_upd = await get_user_data(chat_id); st,btns = main_menu(bd_upd); 
            try: await event.edit(f"Menu Utama\n\n{st}", buttons=btns)
            except MessageNotModifiedError:pass; await event.answer()
            except Exception as e: logger.error(f"Error delete_all_target_groups edit: {e}")
            return
        
        elif data.startswith("delete:"): 
            try:
                _, list_type, _, item_idx_str = data.split(':'); item_idx = int(item_idx_str)
                items = bot_data_cb.get(list_type, [])
                if 0 <= item_idx < len(items): del items[item_idx]; await update_user_data_db(chat_id, bot_data_update={list_type: items}); await event.answer("Item dihapus.")
                else: await event.answer("Indeks tidak valid.")
                _p, _s, bd_upd = await get_user_data(chat_id) 
                await display_paginated_list(event, chat_id, bd_upd, list_type, bot_data_cb.get('current_page_context',{}).get('page',0), 'main_menu', edit_mode=True)
            except Exception as e_del: logger.error(f"Error delete item: {e_del}"); await event.answer("Gagal hapus.")
            return

        elif data.startswith("page:"): 
            try:
                _, list_type, page_num_str, back_menu = data.split(':'); page_num = int(page_num_str)
                await display_paginated_list(event, chat_id, bot_data_cb, list_type, page_num, back_menu, edit_mode=True)
            except Exception as e_page: logger.error(f"Error navigasi halaman: {e_page}"); await event.answer("Gagal navigasi.")
            return
        
        elif data.startswith("send_to_me_"): 
            item_id_stm = data.replace("send_to_me_", "")
            saved_item = next((i for i in bot_data_cb.get('saved_texts', []) if i.get('id') == item_id_stm), None)
            if not saved_item: await event.answer("Item tidak ditemukan."); return
            
            client_to_use_sendme = user_clients.get(chat_id)
            if not client_to_use_sendme and is_admin(chat_id) and bot_data_cb.get('is_registered') and bot_data_cb.get('session_string'):
                 client_to_use_sendme = TelegramClient(StringSession(bot_data_cb.get('session_string')), API_ID, API_HASH, loop=loop)
                 if not await client_to_use_sendme.connect(): await event.answer("Gagal menghubungkan userbot admin!", alert=True); return
            elif not client_to_use_sendme or not client_to_use_sendme.is_connected():
                 await event.answer("Klien userbot tidak aktif!",True); return

            text_sendme = saved_item.get('text'); media_id_sendme = saved_item.get('media_file_id')
            entities_sendme = [dict_to_entity(e) for e in saved_item.get('entities',[]) if e]
            try:
                if media_id_sendme: 
                    try:
                        await client_to_use_sendme.send_file('me', media_id_sendme, caption=text_sendme, formatting_entities=entities_sendme if entities_sendme else None)
                    except TypeError as te: 
                         logger.error(f"TypeError saat send_to_me (media): {te}. Mencoba mengirim teks saja.")
                         if text_sendme: await client_to_use_sendme.send_message('me', f"[Media Gagal Dikirim, Teks Asli]:\n{text_sendme}", formatting_entities=entities_sendme if entities_sendme else None)
                         else: await event.answer("Gagal mengirim media (TypeError) dan tidak ada teks.")
                    except Exception as e_send_media:
                         logger.error(f"Gagal mengirim media ID {media_id_sendme} ke 'me' untuk {chat_id}: {e_send_media}", exc_info=True)
                         if text_sendme: await client_to_use_sendme.send_message('me', f"[Media Gagal Dikirim, Teks Asli]:\n{text_sendme}", formatting_entities=entities_sendme if entities_sendme else None)
                         else: await event.answer("Gagal mengirim media dan tidak ada teks.")
                elif text_sendme: await client_to_use_sendme.send_message('me', text_sendme, formatting_entities=entities_sendme if entities_sendme else None)
                await event.answer("Terkirim ke Pesan Disimpan!")
            except Exception as e_sendme: logger.error(f"Gagal send_to_me: {e_sendme}"); await event.answer("Gagal kirim.")
            finally: 
                if is_admin(chat_id) and client_to_use_sendme and chat_id not in user_clients and client_to_use_sendme.is_connected():
                    await client_to_use_sendme.disconnect()

            st_mm_sm, btns_mm_sm = main_menu(bot_data_cb); 
            try: await event.edit(f"Menu Utama\n\n{st_mm_sm}", buttons=btns_mm_sm)
            except MessageNotModifiedError:pass; await event.answer()
            except Exception as e: logger.error(f"Error send_to_me edit: {e}")
            return

        if bot_data_cb.get('active_key_type') == 'vip':
            if data == "watermark_settings": 
                txt,btns = watermark_settings_menu(bot_data_cb); 
                try: await event.edit(txt, buttons=btns)
                except MessageNotModifiedError:pass; await event.answer()
                except Exception as e: logger.error(f"Error watermark_settings edit: {e}")
                return
            elif data == "toggle_watermark": 
                new_status = not bot_data_cb.get('watermark_enabled', False)
                await update_user_data_db(chat_id, bot_data_update={'watermark_enabled': new_status}); await event.answer(f"Watermark {'diaktifkan' if new_status else 'dinonaktifkan'}.")
                _p, _s, bd_upd = await get_user_data(chat_id); txt,btns = watermark_settings_menu(bd_upd); 
                try: await event.edit(txt, buttons=btns)
                except MessageNotModifiedError:pass; await event.answer()
                except Exception as e: logger.error(f"Error toggle_watermark edit: {e}")
                return
            elif data == "set_watermark_text": 
                await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': 'set_watermark_text_input', 'admin_message_to_edit_id': message_id_cb}); 
                try: await event.edit("Kirim teks watermark baru:")
                except MessageNotModifiedError:pass; await event.answer()
                except Exception as e: logger.error(f"Error set_watermark_text edit: {e}")
                return

    if is_admin(chat_id):
        if data == "admin_panel":
            txt, btns = admin_main_menu(); await event.edit(txt, buttons=btns); return
        elif data == "admin_setup_userbot_prompt": 
            try:
                await event.edit("Anda yakin ingin menyetel userbot pribadi Anda sebagai admin?", 
                                 buttons=[[Button.inline("Ya, Setel Sekarang", "admin_setup_userbot_confirm")],
                                          [Button.inline("Batal", "admin_panel")]])
            except Exception as e: logger.error(f"Error admin_setup_userbot_prompt: {e}"); await event.answer("Gagal.")
            return
        elif data == "admin_setup_userbot_confirm": 
            try:
                await event.delete() 
                await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': 'admin_userbot_setup_contact'})
                await bot.send_message(chat_id, 
                                       "Silakan bagikan kontak Anda sekarang (pilih 'Bagikan Kontak Saya' dari menu lampiran Telegram) untuk menyetel userbot admin.",
                                       buttons=[[Button.inline("Batalkan Setup", "admin_panel")]])
            except Exception as e: logger.error(f"Error admin_setup_userbot_confirm: {e}"); await event.answer("Gagal.")
            return

        elif data == "admin_manage_keys":
            txt, btns = admin_manage_keys_menu(); await event.edit(txt, buttons=btns); return
        elif data == "admin_generate_key_prompt":
            btns_key_type = [[Button.inline("🔑 Basic Key", b"admin_gen_key_basic")], [Button.inline("👑 VIP Key", b"admin_gen_key_vip")], [Button.inline("Kembali", b"admin_manage_keys")]]
            try: await event.edit("Pilih tipe kunci yang ingin digenerate:", buttons=btns_key_type)
            except MessageNotModifiedError:pass; await event.answer()
            except Exception as e: logger.error(f"Error admin_generate_key_prompt edit: {e}")
            return
        elif data == "admin_gen_key_basic":
            await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': 'admin_generate_key_duration', 'admin_temp_key_type': 'basic', 'admin_message_to_edit_id': message_id_cb})
            try: await event.edit("Masukkan durasi untuk Kunci Basic (contoh: 7d, 24h, 60m):")
            except MessageNotModifiedError:pass; await event.answer()
            except Exception as e: logger.error(f"Error admin_gen_key_basic edit: {e}")
            return
        elif data == "admin_gen_key_vip":
            await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': 'admin_generate_key_duration', 'admin_temp_key_type': 'vip', 'admin_message_to_edit_id': message_id_cb})
            try: await event.edit("Masukkan durasi untuk Kunci VIP (contoh: 30d, 720h):")
            except MessageNotModifiedError:pass; await event.answer()
            except Exception as e: logger.error(f"Error admin_gen_key_vip edit: {e}")
            return
        
        elif data == "admin_list_unclaimed_keys" or data == "admin_list_claimed_keys":
            list_type = "unclaimed" if data == "admin_list_unclaimed_keys" else "claimed"
            page = 0 
            await display_admin_keys_list(event, chat_id, list_type, page)
            return
        elif data.startswith("adm_keys_page:"):
            try:
                _, list_type, page_str = data.split(':')
                await display_admin_keys_list(event, chat_id, list_type, int(page_str))
            except Exception as e_pg_key: logger.error(f"Error navigasi halaman kunci admin: {e_pg_key}"); await event.answer("Gagal navigasi.")
            return
        elif data == "admin_revoke_key_input":
            await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': 'admin_revoke_key_value_input', 'admin_message_to_edit_id': message_id_cb})
            try: await event.edit("Masukkan nilai kunci yang ingin dicabut/dihapus:", buttons=[[Button.inline("Kembali", b"admin_manage_keys")]])
            except MessageNotModifiedError:pass; await event.answer()
            except Exception as e: logger.error(f"Error admin_revoke_key_input edit: {e}")
            return

        elif data == "admin_broadcast":
            await update_user_data_db(chat_id, bot_data_update={'awaiting_input_type': 'admin_broadcast_message', 'admin_message_to_edit_id': message_id_cb})
            try: await event.edit("Masukkan pesan broadcast:", buttons=[[Button.inline("Kembali", b"admin_panel")]])
            except MessageNotModifiedError:pass; await event.answer()
            except Exception as e: logger.error(f"Error admin_broadcast edit: {e}")
            return
        elif data == "admin_list_active_users":
            await display_active_users_list(event, chat_id, 0) 
            return
        elif data.startswith("adm_users_page:"):
            try:
                _, page_str = data.split(':')
                await display_active_users_list(event, chat_id, int(page_str))
            except Exception as e_pg_usr: logger.error(f"Error navigasi halaman pengguna admin: {e_pg_usr}"); await event.answer("Gagal navigasi.")
            return

    await event.answer()

# --- Fungsi Tampilan Paginasi untuk User ---
async def display_paginated_list(event, chat_id, bot_data_param, list_type_key, page, back_menu_callback_data, edit_mode=False):
    """Menampilkan daftar item (teks tersimpan, grup target, set link) dengan paginasi untuk pengguna."""
    user_client = user_clients.get(chat_id) 
    if not user_client and is_admin(chat_id) and bot_data_param.get('is_registered') and bot_data_param.get('session_string'): 
        user_client = TelegramClient(StringSession(bot_data_param.get('session_string')), API_ID, API_HASH, loop=loop)
        try:
            if not await user_client.connect(): user_client = None 
        except: user_client = None

    await update_user_data_db(chat_id, bot_data_update={'current_page_context': {'list_type': list_type_key, 'page': page, 'back_menu': back_menu_callback_data}})
    _ph_dpl, _ss_dpl, bot_data_param = await get_user_data(chat_id) 
    
    items_all_dpl = bot_data_param.get(list_type_key, [])
    display_items_info_dpl = []

    for idx, item_val in enumerate(items_all_dpl):
        display_text_dpl = ""
        if list_type_key == 'saved_texts':
            text_content_dpl = item_val.get('text', ''); media_type_dpl = item_val.get('media_file_type')
            media_display = f"[{media_type_dpl.capitalize()}]" if media_type_dpl else ""
            
            if text_content_dpl and media_display: display_text_dpl = f"{media_display} {text_content_dpl[:20]}"
            elif media_display: display_text_dpl = media_display
            elif text_content_dpl: display_text_dpl = text_content_dpl[:25]
            else: display_text_dpl = "[Konten Kosong]"
            if len(display_text_dpl) > 25 : display_text_dpl = display_text_dpl[:22] + "..."

        elif list_type_key == 'forward_sets':
            link_type = item_val.get('type', 'unknown')
            if link_type == 'single':
                display_text_dpl = f"Single: {item_val.get('link', 'N/A')[:30]}..."
            elif link_type == 'dual':
                display_text_dpl = f"Dual: {item_val.get('link1', 'N/A')[:15]} -> {item_val.get('link2', 'N/A')[:15]}... ({item_val.get('delay', 0)}s)"
            else:
                display_text_dpl = str(item_val)[:30] + "..."

        elif list_type_key == 'target_groups':
            if user_client and user_client.is_connected():
                try:
                    entity = await user_client.get_entity(int(item_val) if item_val.lstrip('-').isdigit() else item_val)
                    title = getattr(entity, 'title', str(item_val))
                    username = getattr(entity, 'username', None)
                    display_text_dpl = f"{title}"
                    if username: display_text_dpl += f" (@{username})"
                    display_text_dpl = display_text_dpl[:30]+"..." if len(display_text_dpl) > 30 else display_text_dpl
                except Exception as e_resolve_title:
                    logger.warning(f"Gagal resolve title untuk target grup '{item_val}': {e_resolve_title}")
                    display_text_dpl = str(item_val)[:30]+"..." if len(str(item_val)) > 30 else str(item_val)
            else:
                display_text_dpl = str(item_val)[:30]+"..." if len(str(item_val)) > 30 else str(item_val)
        else: 
            display_text_dpl = str(item_val)[:30]+"..." if len(str(item_val)) > 30 else str(item_val)
        display_items_info_dpl.append({'original_item': item_val, 'display_text': display_text_dpl, 'global_idx': idx})

    if is_admin(chat_id) and user_client and chat_id not in user_clients and user_client.is_connected(): 
        await user_client.disconnect()

    if not display_items_info_dpl:
        empty_message_dpl = "Tidak ada item."
        if list_type_key == 'saved_texts': empty_message_dpl = "Tidak ada teks/media yang disimpan."
        elif list_type_key == 'target_groups': empty_message_dpl = "Tidak ada grup target yang ditambahkan."
        elif list_type_key == 'forward_sets': empty_message_dpl = "Tidak ada link forward yang disimpan."

        buttons_empty_dpl = []
        if list_type_key == 'saved_texts': buttons_empty_dpl.append([Button.inline(f"Simpan Teks/Media", b"save_text_media")])
        elif list_type_key == 'target_groups': buttons_empty_dpl.append([Button.inline("Tambah Grup Target", b"add_group")])
        elif list_type_key == 'forward_sets': buttons_empty_dpl.append([Button.inline("Tambah Link Forward", b"save_link")])
        
        buttons_empty_dpl.append([Button.inline("Kembali", back_menu_callback_data.encode())])
        try:
            if edit_mode: await event.edit(empty_message_dpl, buttons=buttons_empty_dpl)
            else: await event.respond(empty_message_dpl, buttons=buttons_empty_dpl)
        except MessageNotModifiedError: pass; await event.answer()
        except Exception as e: logger.error(f"Error menampilkan daftar kosong '{list_type_key}': {e}", exc_info=True); await event.answer("Gagal menampilkan daftar.", alert=True)
        return

    total_items_dpl, total_pages_dpl = len(display_items_info_dpl), (len(display_items_info_dpl) + ITEMS_PER_PAGE - 1) // ITEMS_PER_PAGE
    page = max(0, min(page, total_pages_dpl - 1)) 
    start_idx_dpl, end_idx_dpl = page * ITEMS_PER_PAGE, min((page + 1) * ITEMS_PER_PAGE, total_items_dpl)
    current_page_items_info_dpl = display_items_info_dpl[start_idx_dpl:end_idx_dpl]
    
    buttons_main_rows_dpl = []
    title_display_map = {
        'saved_texts': "Teks/Media Tersimpan",
        'target_groups': "Grup Target",
        'forward_sets': "Set Link Forward"
    }
    title_display_dpl = title_display_map.get(list_type_key, list_type_key.replace('_', ' ').title())

    list_text_content_dpl = f"Daftar {title_display_dpl} (Halaman {page + 1}/{total_pages_dpl}):\n"

    for item_info_dpl in current_page_items_info_dpl:
        item_display_text_dpl, global_idx_dpl = item_info_dpl['display_text'], item_info_dpl['global_idx']
        list_text_content_dpl += f"\n{start_idx_dpl + current_page_items_info_dpl.index(item_info_dpl) + 1}. {item_display_text_dpl}"
        buttons_main_rows_dpl.append([Button.inline("Hapus", f"delete:{list_type_key}:idx:{global_idx_dpl}".encode())])
    
    nav_buttons_row_dpl = []
    if page > 0: nav_buttons_row_dpl.append(Button.inline("<< Sebelumnya", f"page:{list_type_key}:{page-1}:{back_menu_callback_data}".encode()))
    if page < total_pages_dpl - 1: nav_buttons_row_dpl.append(Button.inline("Berikutnya >>", f"page:{list_type_key}:{page+1}:{back_menu_callback_data}".encode()))
    
    final_buttons_assembly_dpl = buttons_main_rows_dpl
    if nav_buttons_row_dpl: final_buttons_assembly_dpl.append(nav_buttons_row_dpl)
    
    if list_type_key == 'saved_texts': final_buttons_assembly_dpl.append([Button.inline(f"Simpan Teks/Media", b"save_text_media")])
    elif list_type_key == 'target_groups': final_buttons_assembly_dpl.append([Button.inline("Tambah Grup Target", b"add_group")])
    elif list_type_key == 'forward_sets': final_buttons_assembly_dpl.append([Button.inline("Tambah Link Forward", b"save_link")])


    if list_type_key == 'target_groups' and items_all_dpl: final_buttons_assembly_dpl.append([Button.inline("Hapus Semua Grup Target", b"delete_all_target_groups")])
    final_buttons_assembly_dpl.append([Button.inline("Kembali", back_menu_callback_data.encode())])
    
    try:
        if edit_mode: await event.edit(list_text_content_dpl, buttons=final_buttons_assembly_dpl)
        else: await event.respond(list_text_content_dpl, buttons=final_buttons_assembly_dpl)
    except MessageNotModifiedError: pass; await event.answer()
    except FloodWaitError as e: await asyncio.sleep(e.seconds); await event.edit(list_text_content_dpl, buttons=final_buttons_assembly_dpl)
    except ValueError as ve: logger.error(f"ValueError (tombol terlalu panjang) menampilkan daftar: {ve}", exc_info=True); await event.answer("Error: Data tombol terlalu panjang.", alert=True)
    except Exception as e: logger.error(f"Error tidak terduga saat menampilkan daftar berpaginasi: {e}", exc_info=True); await event.answer("Gagal menampilkan daftar.", alert=True)

# --- Fungsi Tampilan Paginasi untuk Admin ---
async def display_admin_keys_list(event, admin_chat_id, list_type, page):
    items_per_page_admin = ADMIN_KEYS_ITEMS_PER_PAGE 
    
    query = "SELECT key_value, key_type, generation_timestamp, duration_seconds, assigned_watermark_text, claimed_by_chat_id, claim_timestamp FROM access_keys WHERE "
    query += "is_claimed = FALSE" if list_type == "unclaimed" else "is_claimed = TRUE"
    query += " ORDER BY generation_timestamp DESC" 

    try:
        async with db_pool.acquire() as conn:
            all_keys_records = await conn.fetch(query)
    except Exception as e_fetch_keys:
        logger.error(f"Gagal mendapatkan daftar kunci admin ({list_type}): {e_fetch_keys}")
        _t, btns_km = admin_manage_keys_menu(); await event.edit(f"Gagal mendapatkan daftar kunci ({list_type}).\n{_t}", buttons=btns_km); return

    if not all_keys_records:
        _t, btns_km = admin_manage_keys_menu(); await event.edit(f"Tidak ada kunci yang {list_type} ditemukan.\n{_t}", buttons=btns_km); return

    total_items = len(all_keys_records)
    total_pages = (total_items + items_per_page_admin - 1) // items_per_page_admin
    page = max(0, min(page, total_pages - 1))
    start_idx = page * items_per_page_admin
    end_idx = min((page + 1) * items_per_page_admin, total_items)
    
    page_items = all_keys_records[start_idx:end_idx]
    
    text_content = f"Daftar Kunci {list_type.capitalize()} (Halaman {page + 1}/{total_pages}):\n"
    for item in page_items:
        gen_time = datetime.datetime.fromtimestamp(item['generation_timestamp']).strftime('%y-%m-%d %H:%M')
        key_val_short = item['key_value'][:8] + "..."
        dur_s = item['duration_seconds']
        dur_text = f"{dur_s // 86400}d" if dur_s % 86400 == 0 and dur_s >= 86400 else f"{dur_s // 3600}h" if dur_s % 3600 == 0 and dur_s >=3600 else f"{dur_s // 60}m"
        
        text_content += f"\n- `{key_val_short}` ({item['key_type'].upper()}), Dur: {dur_text}, Gen: {gen_time}"
        if list_type == "claimed" and item['claimed_by_chat_id']:
            claim_time_str = datetime.datetime.fromtimestamp(item['claim_timestamp']).strftime('%y-%m-%d %H:%M')
            user_expiry_ts = item['claim_timestamp'] + item['duration_seconds']
            user_expiry_str = datetime.datetime.fromtimestamp(user_expiry_ts).strftime('%y-%m-%d %H:%M')
            text_content += f"\n  Diklaim oleh: {item['claimed_by_chat_id']} ({claim_time_str}). Exp User: {user_expiry_str}"
        elif list_type == "unclaimed" and item['key_type'] == 'basic' and item['assigned_watermark_text']:
             text_content += f"\n  WM Basic: \"{item['assigned_watermark_text'][:20]}...\""
    
    buttons = []
    nav_row = []
    if page > 0: nav_row.append(Button.inline("<< Sebelumnya", f"adm_keys_page:{list_type}:{page-1}"))
    if page < total_pages - 1: nav_row.append(Button.inline("Berikutnya >>", f"adm_keys_page:{list_type}:{page+1}"))
    if nav_row: buttons.append(nav_row)
    buttons.append([Button.inline("Kembali ke Kelola Kunci", b"admin_manage_keys")])
    
    try: await event.edit(text_content, buttons=buttons, parse_mode='md')
    except MessageNotModifiedError: await event.answer()
    except Exception as e_edit_keys: logger.error(f"Error edit daftar kunci admin: {e_edit_keys}"); await event.answer("Gagal menampilkan daftar.")

async def display_active_users_list(event, admin_chat_id, page):
    items_per_page_admin = ADMIN_KEYS_ITEMS_PER_PAGE 
    current_ts = int(time.time())
    
    try:
        async with db_pool.acquire() as conn:
            all_users_records = await conn.fetch("SELECT chat_id, bot_data FROM users")
    except Exception as e_fetch_users:
        logger.error(f"Gagal mendapatkan daftar pengguna: {e_fetch_users}")
        _t,btns_am = admin_main_menu(); await event.edit(f"Gagal mendapatkan daftar pengguna.\n{_t}", buttons=btns_am); return

    active_users_info = []
    for record in all_users_records:
        chat_id = record['chat_id']
        if is_admin(chat_id): continue 

        bot_data = json.loads(record['bot_data']) if record['bot_data'] else {}
        if bot_data.get('has_valid_key') and bot_data.get('key_expiry_timestamp', 0) > current_ts:
            active_users_info.append({
                'chat_id': chat_id,
                'key_type': bot_data.get('active_key_type', 'N/A'),
                'key_value': bot_data.get('active_key_value', 'N/A')[:10]+"...",
                'expiry_ts': bot_data.get('key_expiry_timestamp')
            })
    
    active_users_info.sort(key=lambda x: x['expiry_ts'])

    if not active_users_info:
        _t,btns_am = admin_main_menu(); await event.edit(f"Tidak ada pengguna aktif (dengan kunci valid) yang ditemukan.\n{_t}", buttons=btns_am); return

    total_items = len(active_users_info)
    total_pages = (total_items + items_per_page_admin - 1) // items_per_page_admin
    page = max(0, min(page, total_pages - 1))
    start_idx = page * items_per_page_admin
    end_idx = min((page + 1) * items_per_page_admin, total_items)
    
    page_items = active_users_info[start_idx:end_idx]
    
    text_content = f"Pengguna Aktif (Halaman {page + 1}/{total_pages}):\n"
    for item in page_items:
        expiry_str = datetime.datetime.fromtimestamp(item['expiry_ts']).strftime('%Y-%m-%d %H:%M')
        text_content += f"\n- ID: {item['chat_id']}\n  Tipe: {item['key_type'].upper()}, Kunci: `{item['key_value']}`\n  Kadaluwarsa: {expiry_str}\n"
    
    buttons = []
    nav_row = []
    if page > 0: nav_row.append(Button.inline("<< Sebelumnya", f"adm_users_page:{page-1}"))
    if page < total_pages - 1: nav_row.append(Button.inline("Berikutnya >>", f"adm_users_page:{page+1}"))
    if nav_row: buttons.append(nav_row)
    buttons.append([Button.inline("Kembali ke Panel Admin", b"admin_panel")])
    
    try: await event.edit(text_content, buttons=buttons, parse_mode='md')
    except MessageNotModifiedError: await event.answer()
    except Exception as e_edit_users: logger.error(f"Error edit daftar pengguna aktif: {e_edit_users}"); await event.answer("Gagal menampilkan daftar.")

# --- Fungsi Inti (Copy) dengan Watermark ---
async def send_messages_in_batches(user_client, groups_to_send_to, message_func, chat_id, action_name, item_to_send=None):
    if not user_client: 
        logger.error(f"send_messages_in_batches dipanggil dengan user_client None untuk {chat_id}")
        await bot.send_message(chat_id, "Error internal: Klien pengguna tidak tersedia untuk mengirim pesan.")
        return False 

    successful_groups, failed_groups_details, groups_to_remove_runtime = [], [], []
    
    valid_targets_peer_ids, invalid_target_details = [], [] 
    if not groups_to_send_to: 
        logger.info(f"Tidak ada grup target disediakan untuk {action_name} oleh {chat_id}")
        await bot.send_message(chat_id, f"Tidak ada grup target yang disetel untuk {action_name.lower()}.")
        return True 

    for target_id_val_orig_str in groups_to_send_to: 
        is_valid_val, entity_or_error_msg = await validate_entity(user_client, target_id_val_orig_str, chat_id, group_only=True)
        if is_valid_val and entity_or_error_msg: 
            try:
                peer_id_int = get_peer_id(entity_or_error_msg)
                valid_targets_peer_ids.append(peer_id_int) 
            except Exception as e_get_peer:
                logger.error(f"Gagal mendapatkan peer_id dari entitas {entity_or_error_msg} untuk {target_id_val_orig_str}: {e_get_peer}")
                invalid_target_details.append((target_id_val_orig_str, "Gagal mendapatkan Peer ID"))
        else: 
            invalid_target_details.append((target_id_val_orig_str, entity_or_error_msg if isinstance(entity_or_error_msg, str) else "Validasi Gagal"))
            logger.warning(f"Target tidak valid {target_id_val_orig_str} untuk {chat_id}: {entity_or_error_msg if isinstance(entity_or_error_msg, str) else 'Objek entitas tidak kembali'}")

    if invalid_target_details:
        _ph_inv, _ss_inv, bot_data_inv_rem = await get_user_data(chat_id)
        current_target_groups_db_inv = list(bot_data_inv_rem.get('target_groups', []))
        ids_invalid_orig = [inv_tg[0] for inv_tg in invalid_target_details] 
        
        updated_target_groups_list_inv = [tg for tg in current_target_groups_db_inv if tg not in ids_invalid_orig]
        
        if len(updated_target_groups_list_inv) < len(current_target_groups_db_inv):
            await update_user_data_db(chat_id, bot_data_update={'target_groups': updated_target_groups_list_inv})
            await bot.send_message(chat_id, f"{len(invalid_target_details)} target tidak valid dihapus dari daftar Anda: {', '.join(map(str,ids_invalid_orig[:3]))}{'...' if len(ids_invalid_orig)>3 else ''}")

    if not valid_targets_peer_ids: 
        await bot.send_message(chat_id, f"Tidak ada grup target valid yang ditemukan untuk {action_name.lower()}. Pastikan Anda telah menambahkan grup yang benar.")
        return True

    progress_msg_obj = None
    try: progress_msg_obj = await bot.send_message(chat_id, f"Memulai {action_name.lower()} ke {len(valid_targets_peer_ids)} target...")
    except Exception as e: logger.error(f"Gagal mengirim pesan progres: {e}", exc_info=True)

    total_batches = (len(valid_targets_peer_ids) + BATCH_SIZE - 1) // BATCH_SIZE

    for batch_idx in range(total_batches):
        start_idx_batch, end_idx_batch = batch_idx * BATCH_SIZE, min((batch_idx + 1) * BATCH_SIZE, len(valid_targets_peer_ids))
        current_batch_targets_peer_ids = valid_targets_peer_ids[start_idx_batch:end_idx_batch] 
        try: 
            if progress_msg_obj: await progress_msg_obj.edit(f"Batch {batch_idx+1}/{total_batches} ({len(current_batch_targets_peer_ids)} target)... {action_name}")
        except MessageNotModifiedError: pass
        except FloodWaitError as e_flood_edit: await asyncio.sleep(e_flood_edit.seconds + 1) 
        except Exception as e_edit_prog: logger.error(f"Gagal mengedit pesan progres: {e_edit_prog}", exc_info=True)

        for target_peer_id_int in current_batch_targets_peer_ids: 
            if not user_client.is_connected():
                logger.warning(f"Klien pengguna {chat_id} terputus. Memeriksa sesi.")
                if not await verify_session(user_client, chat_id):
                    logger.error(f"Klien pengguna {chat_id} gagal diverifikasi. Menghentikan pengiriman.")
                    return False 
                logger.info(f"Klien pengguna {chat_id} terhubung kembali.")

            try:
                logger.info(f"Mencoba {action_name} ke ID peer {target_peer_id_int} untuk {chat_id}")
                await message_func(user_client, target_peer_id_int, item_to_send) 
                successful_groups.append(target_peer_id_int)
                logger.info(f"Berhasil {action_name} ke ID peer {target_peer_id_int} untuk {chat_id}")
                await asyncio.sleep(2.5) 
            except FloodWaitError as e_flood_send:
                wait_duration = e_flood_send.seconds * 1.5 
                logger.warning(f"FloodWait ke {target_peer_id_int} untuk {chat_id}. Menunggu {wait_duration:.0f}s...")
                await bot.send_message(chat_id, f"Kena FloodWait saat mengirim ke {target_peer_id_int}. Menunggu {wait_duration:.0f} detik...")
                await asyncio.sleep(wait_duration)
                try: 
                    await message_func(user_client, target_peer_id_int, item_to_send)
                    successful_groups.append(target_peer_id_int)
                except Exception as e_retry_flood:
                    logger.error(f"Gagal retry pengiriman setelah FloodWait ke {target_peer_id_int} untuk {chat_id}: {e_retry_flood}", exc_info=True)
                    if target_peer_id_int not in [fg[0] for fg in failed_groups_details]: failed_groups_details.append((target_peer_id_int, str(e_retry_flood)))
            except (ChatWriteForbiddenError, ChatRestrictedError, UserBannedInChannelError) as e_perm_send:
                error_msg_for_user = f"Gagal mengirim ke {target_peer_id_int}: {type(e_perm_send).__name__}. Pastikan userbot Anda memiliki izin."
                logger.warning(f"{error_msg_for_user} (Pengguna: {chat_id})")
                await bot.send_message(chat_id, error_msg_for_user)
                if target_peer_id_int not in [fg[0] for fg in failed_groups_details]: failed_groups_details.append((target_peer_id_int, str(e_perm_send)))
            except (ChannelPrivateError, ChatAdminRequiredError, UserIsBlockedError, UserNotMutualContactError, UserPrivacyRestrictedError) as e_fatal_access:
                error_msg_for_user = f"Gagal mengakses {target_peer_id_int}: {type(e_fatal_access).__name__}. Grup ini akan dihapus dari daftar Anda."
                logger.error(f"{error_msg_for_user} (Pengguna: {chat_id})")
                await bot.send_message(chat_id, error_msg_for_user)
                if target_peer_id_int not in [fg[0] for fg in failed_groups_details]: failed_groups_details.append((target_peer_id_int, str(e_fatal_access)))
                
                _p_temp, _s_temp, bd_temp = await get_user_data(chat_id)
                original_target_str_to_remove = None
                for tg_str in bd_temp.get('target_groups', []):
                    try:
                        resolved_tg_entity = await user_client.get_entity(int(tg_str) if tg_str.lstrip('-').isdigit() else tg_str)
                        if get_peer_id(resolved_tg_entity) == target_peer_id_int:
                            original_target_str_to_remove = tg_str
                            break
                    except: continue
                if original_target_str_to_remove and original_target_str_to_remove not in groups_to_remove_runtime:
                     groups_to_remove_runtime.append(original_target_str_to_remove)

            except ConnectionError as e_conn_send:
                logger.warning(f"ConnectionError saat mengirim ke {target_peer_id_int} untuk {chat_id}: {e_conn_send}. Memeriksa sesi.")
                if not await verify_session(user_client, chat_id):
                    logger.error(f"Klien untuk {chat_id} gagal diverifikasi. Sesi tidak dapat dipulihkan.")
                    return False 
                continue 
            except ValueError as ve: 
                logger.error(f"ValueError saat mengirim ke {target_peer_id_int} untuk {chat_id}: {ve}", exc_info=True)
                if target_peer_id_int not in [fg[0] for fg in failed_groups_details]: failed_groups_details.append((target_peer_id_int, str(ve)))
            except Exception as e_general_send:
                logger.error(f"Error umum saat mengirim ke {target_peer_id_int} untuk {chat_id}: {e_general_send}", exc_info=True)
                if target_peer_id_int not in [fg[0] for fg in failed_groups_details]: failed_groups_details.append((target_peer_id_int, str(e_general_send)))
        
        if batch_idx < total_batches - 1: await asyncio.sleep(BATCH_DELAY) 

    if groups_to_remove_runtime: 
        _ph_rem_run, _ss_rem_run, bot_data_rem_run = await get_user_data(chat_id)
        current_targets_db_run = list(bot_data_rem_run.get('target_groups', []))
        updated_targets_run = [tg for tg in current_targets_db_run if tg not in groups_to_remove_runtime]
        
        if len(updated_targets_run) < len(current_targets_db_run):
            await update_user_data_db(chat_id, bot_data_update={'target_groups': updated_targets_run})
            removed_groups_str_run = ", ".join(map(str, groups_to_remove_runtime[:5])) + ("..." if len(groups_to_remove_runtime) > 5 else "")
            await bot.send_message(chat_id, f"{len(groups_to_remove_runtime)} grup dihapus karena masalah akses fundamental. Grup: {removed_groups_str_run}.")

    summary_text_final = f"{action_name} selesai.\nBerhasil: {len(successful_groups)}.\nGagal (percobaan kirim): {len(failed_groups_details)}.\n"
    if failed_groups_details:
        summary_text_final += "Rincian Gagal (max 3):\n"
        for i, (grp, err) in enumerate(failed_groups_details[:3]):
            summary_text_final += f"- {grp}: {str(err)[:50]}\n"

    if progress_msg_obj:
        try: await progress_msg_obj.edit(summary_text_final)
        except Exception: await bot.send_message(chat_id, summary_text_final)
    else: await bot.send_message(chat_id, summary_text_final)
    return True

async def forward_and_copy_task(chat_id):
    """Tugas latar belakang untuk meneruskan dan menyalin pesan."""
    logger.info(f"Tugas forward & copy dimulai untuk {chat_id}")
    
    while True:
        try:
            _phone, _session, bot_data = await get_user_data(chat_id)
            current_client = user_clients.get(chat_id)

            if not current_client or not current_client.is_connected():
                logger.warning(f"Klien untuk {chat_id} tidak terhubung di awal loop task. Mencoba memulihkan.")
                if not await verify_session(current_client, chat_id):
                    logger.error(f"Gagal memulihkan sesi untuk {chat_id} di dalam task. Menghentikan.")
                    await update_user_data_db(chat_id, bot_data_update={'is_forwarding': False, 'is_copying': False})
                    break # Hentikan loop task jika sesi gagal
                bot_data = (await get_user_data(chat_id))[2] # Muat ulang data setelah pulih

            # --- Cek Kedaluwarsa Mode ---
            now = int(time.time())
            made_changes = False
            if bot_data.get('is_forwarding') and bot_data.get('forward_expiry_timestamp') and now >= bot_data.get('forward_expiry_timestamp'):
                bot_data['is_forwarding'] = False
                bot_data['forward_expiry_timestamp'] = None
                made_changes = True
                await bot.send_message(chat_id, "Waktu untuk mode Forward telah berakhir.")
            
            if bot_data.get('is_copying') and bot_data.get('copy_expiry_timestamp') and now >= bot_data.get('copy_expiry_timestamp'):
                bot_data['is_copying'] = False
                bot_data['copy_expiry_timestamp'] = None
                made_changes = True
                await bot.send_message(chat_id, "Waktu untuk mode Copy telah berakhir.")
            
            if made_changes:
                await update_user_data_db(chat_id, bot_data_update=bot_data)
            
            # --- Periksa Kondisi Loop ---
            if not (bot_data.get('is_forwarding') or bot_data.get('is_copying')):
                logger.info(f"Tidak ada mode aktif untuk {chat_id}. Menghentikan task.")
                break

            target_groups = bot_data.get('target_groups', [])
            if not target_groups:
                logger.info(f"Tidak ada grup target untuk {chat_id}, menunggu.")
                await asyncio.sleep(bot_data.get('delay', 120))
                continue

            # --- Logika Forward ---
            if bot_data.get('is_forwarding') and bot_data.get('forward_sets'):
                for fwd_set in bot_data.get('forward_sets'):
                    if fwd_set.get('type') == 'single':
                        link = fwd_set.get('link')
                        if not link: continue
                        try:
                            msg_parts = link.split('/')
                            from_chat = msg_parts[-2]
                            msg_id = int(msg_parts[-1])
                            async def do_forward(client, to_chat_id, _): # _ adalah placeholder untuk item_to_send
                                await client.forward_messages(to_chat_id, msg_id, from_chat)
                            if not await send_messages_in_batches(current_client, target_groups, do_forward, chat_id, "Forward Single Link", item_to_send=None):
                                await update_user_data_db(chat_id, bot_data_update={'is_forwarding': False}); break
                        except Exception as e: await bot.send_message(chat_id, f"Error memproses single link {link}: {e}")
                    
                    elif fwd_set.get('type') == 'dual':
                        link1, link2, local_delay = fwd_set.get('link1'), fwd_set.get('link2'), fwd_set.get('delay', 1)
                        if not link1 or not link2: continue
                        try:
                            msg_parts1 = link1.split('/'); from_chat1 = msg_parts1[-2]; msg_id1 = int(msg_parts1[-1])
                            msg_parts2 = link2.split('/'); from_chat2 = msg_parts2[-2]; msg_id2 = int(msg_parts2[-1])
                            async def do_dual_forward(client, to_chat_id, _):
                                await client.forward_messages(to_chat_id, msg_id1, from_chat1)
                                await asyncio.sleep(local_delay)
                                await client.forward_messages(to_chat_id, msg_id2, from_chat2)
                            if not await send_messages_in_batches(current_client, target_groups, do_dual_forward, chat_id, "Forward Dual Link", item_to_send=None):
                                await update_user_data_db(chat_id, bot_data_update={'is_forwarding': False}); break
                        except Exception as e: await bot.send_message(chat_id, f"Error memproses dual link: {e}")
                    await asyncio.sleep(1) # Jeda kecil antar set link
                
            # --- Logika Copy ---
            if bot_data.get('is_copying') and bot_data.get('saved_texts'):
                item_to_copy = bot_data['saved_texts'][0]
                
                async def do_copy_actual(client, to_chat_id, item_to_process_original):
                    item_to_process = copy.deepcopy(item_to_process_original) 
                    text_to_send = item_to_process.get('text', "") 
                    entities_original = item_to_process.get('entities', [])
                    media_id_to_send = item_to_process.get('media_file_id')
                    
                    watermark_to_apply = ""
                    key_type = bot_data.get('active_key_type')

                    if key_type == 'vip' and bot_data.get('watermark_enabled', False):
                        watermark_to_apply = bot_data.get('watermark_text', DEFAULT_GLOBAL_WATERMARK_TEXT)
                    elif key_type == 'basic' and bot_data.get('assigned_basic_watermark_text'):
                        watermark_to_apply = bot_data.get('assigned_basic_watermark_text')
                    elif is_admin(chat_id) and bot_data.get('watermark_enabled', False): 
                         watermark_to_apply = bot_data.get('watermark_text', DEFAULT_GLOBAL_WATERMARK_TEXT)

                    if watermark_to_apply:
                        if text_to_send: text_to_send = f"{text_to_send}\n\n{watermark_to_apply}"
                        elif media_id_to_send: text_to_send = watermark_to_apply 
                    
                    final_entities = None; final_parse_mode = None
                    if watermark_to_apply and entities_original:
                        if re.search(r"[*_`~[\]()]", text_to_send): final_parse_mode = 'md'
                    elif not watermark_to_apply and entities_original:
                        final_entities = [dict_to_entity(e) for e in entities_original if e]; final_entities = [e for e in final_entities if e is not None]
                    elif text_to_send and re.search(r"\[.*?\]\(https?://.*?\)", text_to_send): final_parse_mode = 'md'
                    
                    send_params = {'link_preview': False}
                    if final_entities: send_params['formatting_entities'] = final_entities
                    if final_parse_mode: send_params['parse_mode'] = final_parse_mode
                    
                    if media_id_to_send:
                        await client.send_file(to_chat_id, media_id_to_send, caption=text_to_send, **send_params)
                    elif text_to_send: 
                        await client.send_message(to_chat_id, text_to_send, **send_params)
                    else: logger.warning(f"Tidak ada yang dikirim ke {to_chat_id} untuk item: {item_to_process.get('id')}")

                if not await send_messages_in_batches(current_client, target_groups, do_copy_actual, chat_id, "Copy Konten", item_to_send=item_to_copy):
                    await update_user_data_db(chat_id, bot_data_update={'is_copying': False}); break

            gc.collect()
            await asyncio.sleep(bot_data.get('delay', 120))
        except asyncio.CancelledError:
            logger.info(f"Tugas untuk {chat_id} dibatalkan.")
            break
        except Exception as e:
            logger.error(f"Error kritis di forward_and_copy_task untuk {chat_id}: {e}", exc_info=True)
            try: await bot.send_message(chat_id, f"Terjadi error kritis: {str(e)[:100]}. Tugas dihentikan.")
            except: pass
            await update_user_data_db(chat_id, bot_data_update={'is_forwarding': False, 'is_copying': False})
            break
    
    # Hapus dari dict task setelah loop selesai
    if chat_id in user_tasks:
        del user_tasks[chat_id]
    logger.info(f"Tugas untuk {chat_id} telah berakhir.")


# --- Fungsi Periodik ---
async def clean_cache(): 
    while True:
        try:
            # ... (logika pembersihan cache)
            await asyncio.sleep(CACHE_TTL) 
        except Exception as e_clean_cache: logger.error(f"Error membersihkan cache: {e_clean_cache}", exc_info=True); await asyncio.sleep(CACHE_TTL * 2)

async def check_user_keys_and_sessions():
    await asyncio.sleep(60) 
    while True:
        logger.info("Memulai pemeriksaan periodik kunci pengguna dan sesi...")
        current_ts = int(time.time())
        try:
            async with db_pool.acquire() as conn:
                users_with_keys = await conn.fetch("SELECT chat_id, bot_data FROM users WHERE (bot_data->>'has_valid_key')::boolean = TRUE")

            for user_record in users_with_keys:
                chat_id_check = user_record['chat_id']
                if is_admin(chat_id_check): continue 

                bot_data_check = json.loads(user_record['bot_data']) if user_record['bot_data'] else {}
                key_expiry_ts = bot_data_check.get('key_expiry_timestamp')
                is_userbot_registered = bot_data_check.get('is_registered', False)

                if key_expiry_ts and current_ts >= key_expiry_ts:
                    logger.info(f"Kunci untuk pengguna {chat_id_check} telah kedaluwarsa. Menghapus akses.")
                    try: await bot.send_message(chat_id_check, "Maaf, kunci akses Anda telah kedaluwarsa.")
                    except: pass 
                    await logout_user(chat_id_check, "KEY_EXPIRED") 
                    await update_user_data_db(chat_id_check, bot_data_update={'awaiting_input_type': None, 'has_valid_key': False}) 
                    continue 

                if is_userbot_registered:
                    user_client_check = user_clients.get(chat_id_check)
                    if not user_client_check: 
                        _ph_rec, _ss_rec, _bd_rec = await get_user_data(chat_id_check)
                        if _ss_rec:
                             user_client_check = TelegramClient(StringSession(_ss_rec), API_ID, API_HASH, loop=loop)
                             user_clients[chat_id_check] = user_client_check
                        else: 
                            await update_user_data_db(chat_id_check, bot_data_update={'is_registered': False})
                            continue 

                    if user_client_check and (not await ensure_connected(user_client_check, chat_id_check) or \
                       not await verify_session(user_client_check, chat_id_check)):
                        logger.warning(f"Sesi userbot untuk {chat_id_check} tidak valid. Coba reconnect.")
                        if not await reconnect_client(user_client_check, chat_id_check):
                            logger.error(f"Gagal reconnect userbot untuk {chat_id_check}. Logout userbot.")
                            await update_user_data_db(chat_id_check, bot_data_update={'is_registered': False, 'session_string': None})
                            try: await bot.send_message(chat_id_check, "Sesi userbot Anda terputus. Silakan login kembali.")
                            except:pass

                if bot_data_check.get('has_valid_key') and bot_data_check.get('is_registered') and (is_admin(chat_id_check) or bot_data_check.get('key_expiry_timestamp',0) > current_ts):
                    await manage_forward_copy_task(chat_id_check, bot_data_check)
                await asyncio.sleep(0.2) 
        except Exception as e_periodic_keys:
            logger.error(f"Error dalam pemeriksaan periodik kunci/sesi: {e_periodic_keys}", exc_info=True)
        
        logger.info(f"Pemeriksaan periodik kunci/sesi selesai. Berikutnya dalam {KEY_CHECK_INTERVAL // 60} menit.")
        await asyncio.sleep(KEY_CHECK_INTERVAL)

async def reconnect_client(client_instance_rc, chat_id_rc, max_attempts_rc=2): 
    if not client_instance_rc: return False 
    attempt_rc = 0
    while attempt_rc < max_attempts_rc:
        attempt_rc += 1
        try:
            logger.info(f"Mencoba menghubungkan kembali klien untuk {chat_id_rc} (percobaan {attempt_rc}/{max_attempts_rc})...")
            if not client_instance_rc.is_connected(): 
                await client_instance_rc.connect()
            
            if await client_instance_rc.is_user_authorized(): 
                logger.info(f"Klien untuk {chat_id_rc} terhubung kembali dan terotorisasi.")
                return True
            else: 
                logger.warning(f"Klien untuk {chat_id_rc} terhubung kembali tapi TIDAK terotorisasi.")
                await update_user_data_db(chat_id_rc, bot_data_update={'is_registered': False, 'session_string': None})
                try: await bot.send_message(chat_id_rc, "Sesi userbot Anda tidak valid setelah mencoba menghubungkan kembali.")
                except:pass
                return False 
        except (UserDeactivatedBanError, AuthKeyUnregisteredError, SessionRevokedError) as e_fatal_recon:
            logger.error(f"Error sesi fatal saat menghubungkan kembali untuk {chat_id_rc}: {e_fatal_recon}. Logout userbot.")
            await update_user_data_db(chat_id_rc, bot_data_update={'is_registered': False, 'session_string': None})
            try: await bot.send_message(chat_id_rc, "Sesi userbot Anda tidak dapat dipulihkan (masalah fatal).")
            except:pass
            return False
        except ConnectionError as e_conn_recon:
            logger.error(f"Masalah koneksi saat menghubungkan kembali {chat_id_rc} (percobaan {attempt_rc}): {e_conn_recon}")
            if attempt_rc < max_attempts_rc: await asyncio.sleep(min(2 ** attempt_rc, 15)) 
            else: return False
        except Exception as e_rc:
            logger.error(f"Error tidak terduga saat menghubungkan kembali {chat_id_rc} (percobaan {attempt_rc}): {e_rc}", exc_info=True)
            if attempt_rc < max_attempts_rc: await asyncio.sleep(min(2 ** attempt_rc, 15))
            else: return False
    return False 

async def main():
    try: await init_db()
    except Exception as e_db_init: return 

    try:
        if db_pool:
            async with db_pool.acquire() as conn_main:
                await conn_main.execute(
                    """
                    UPDATE users
                    SET bot_data = bot_data - 'is_registered' - 'session_string' || jsonb_build_object('is_registered', false, 'session_string', null)
                    WHERE (bot_data->>'is_registered')::boolean = TRUE OR bot_data->>'session_string' IS NOT NULL;
                    """
                )
                logger.info("Semua sesi userbot yang ada telah direset di DB (is_registered=false, session_string=null). Info kunci dijaga.")
                user_clients.clear()
                for task_key in list(user_tasks.keys()): 
                    if user_tasks[task_key] and not user_tasks[task_key].done():
                        user_tasks[task_key].cancel()
                    del user_tasks[task_key] 
                user_data_cache.clear() 
    except Exception as e_startup_reset:
        logger.critical(f"Error kritis saat mereset sesi userbot di startup: {e_startup_reset}", exc_info=True)

    asyncio.create_task(clean_cache())
    asyncio.create_task(check_user_keys_and_sessions()) 
    
    try:
        logger.info("Memulai bot utama...")
        await bot.start(bot_token=BOT_TOKEN)
        logger.info("Bot utama berhasil dimulai.")
        await bot.run_until_disconnected()
    except Exception as e_main_run: logger.critical(f"Error kritis di fungsi utama: {e_main_run}", exc_info=True)
    finally:
        logger.info("Bot sedang dimatikan...")
        for client_id_shutdown_val in list(user_clients.keys()): 
            client_instance = user_clients.get(client_id_shutdown_val)
            if client_instance and client_instance.is_connected():
                try: await client_instance.disconnect()
                except: pass 
            if client_id_shutdown_val in user_clients: del user_clients[client_id_shutdown_val]
        
        for task_key_shutdown in list(user_tasks.keys()): 
            if user_tasks[task_key_shutdown] and not user_tasks[task_key_shutdown].done():
                user_tasks[task_key_shutdown].cancel()
            del user_tasks[task_key_shutdown] 

        if bot.is_connected():
            try: await bot.disconnect()
            except: pass
        
        if db_pool: await db_pool.close()
        logger.info("Bot telah dimatikan.")

if __name__ == '__main__':
    try: loop.run_until_complete(main())
    except KeyboardInterrupt: logger.info("Proses diinterupsi.")
    finally:
        if loop and not loop.is_closed():
            current_tasks = asyncio.all_tasks(loop=loop)
            for task_item in current_tasks:
                if task_item is not asyncio.current_task(loop=loop) and not task_item.done():
                    task_item.cancel()
            try:
                if current_tasks: 
                     loop.run_until_complete(asyncio.gather(*[t for t in current_tasks if not t.done()], return_exceptions=True))
            except Exception as e_gather:
                 logger.error(f"Error saat mengumpulkan task yang dibatalkan: {e_gather}")
            finally:
                 logger.info("Menutup event loop.")
                 loop.close()
