"""
Voice Channel Silence Bot
==========================

Seven slash commands:

  /silence    Denies the @everyone role the "Speak" permission in the voice
              channel the invoking member is currently connected to. This
              never server-mutes anyone -- it only edits that one channel's
              permission overwrite for @everyone. Every other permission on
              that overwrite, and every other role's or member's overwrite
              (for example an explicit Speak allow on a "Guild Master"
              role), is left completely untouched.

  /unsilence  Restores @everyone's Speak permission in a voice channel to
              exactly what it was before /silence was used on it: Allow,
              Deny, or "not set" (inherited) -- whichever it originally was.
              Defaults to the channel the invoking member is connected to,
              or accepts an explicit channel argument.

  /unverified Lists the members who currently have the Unverified role, as
              plain-text display names (not clickable mentions, so nobody is
              pinged and the names always show correctly) with a count, in
              the channel where it was used. Read-only: it never changes any
              member or role. Requires Manage Channels.

  /mute       Server-mutes a member who is in a voice channel for a chosen
              time (1 minute to 24 hours) and lifts the mute automatically
              at the saved end time, even across restarts. Requires Mute
              Members. Every mute, expiry and early release is written to
              the moderation-log channel (MOD_LOG_CHANNEL_ID). Records are
              kept in their own file (MUTE_STATE_PATH), never in
              silence_state.json.

  /unmute     Ends a /mute early. Only touches mutes created by /mute.
              Requires Mute Members.

  /tkl        Verifies a member: first shows the moderator a private, ephemeral
              choice between Full Access (The Kings Legion role) and Limited
              Access (voice channels only) -- nothing changes until one is
              picked. Then removes their Unverified role, gives whichever role
              was chosen, posts a public approval message that pings them
              (with an optional note from the moderator), and writes an audit
              entry -- including which access level was given -- to the
              mod-log channel. Only members with one of the staff roles in
              TKL_STAFF_ROLE_IDS can use it; that role list is the only
              authorisation check.

  /commands   Lists this bot's commands and what they do. Open to everyone.

  /define     Looks a word or phrase up in Merriam-Webster's Collegiate
              Dictionary and shows its definitions in the channel. Needs the
              MERRIAM_WEBSTER_API_KEY environment variable; without it the
              command says it isn't set up and nothing else is affected.
              Open to everyone.

  /urban      Posts an Urban Dictionary search link for a word or phrase. It
              only builds the link: no API key, nothing is fetched. It works
              in every channel and is deliberately not NSFW-only. Open to
              everyone.

Not a command: while the bot runs, an observe-only background check looks at
esoserverstatus.net every couple of minutes and posts what it sees (the rows for
each megaserver and the page's own HTML around them) to one channel in the test
server, ESO_OBSERVER_CHANNEL_ID. It announces nothing and keeps no file. Its only
ping is to ESO_OBSERVER_PING_USER_ID, when it posts a warning. Set the ESO_OBSERVER
environment variable to "off" to switch it off.

Also in the background: an Xbox status monitor watches the XBOX EU and XBOX NA rows of that same page and announces when
either one goes down or comes back, in a test channel only until you switch it to the main server (see the section "ESO
Xbox server status" below). /server (EU or NA) shows the current status, and /server-sim posts a clearly labelled
simulation in the test server. Both exist only in the servers named in ESO_STATUS_TEST_GUILD_ID and ESO_STATUS_MAIN_GUILD_ID.

Requires Python 3.8+ and discord.py 2.4+. /unverified also needs the
privileged Server Members Intent (see "Bot setup" below, and enable it in
the Discord Developer Portal too). See README.md for setup, invite-link,
and deployment instructions.
"""

import asyncio
import contextlib
import html
import json
import logging
import os
import re
import secrets
import shutil
import time
import traceback
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

import discord
from discord import app_commands
from discord.ext import commands
from dotenv import load_dotenv

load_dotenv()  # Loads a local .env file if present; harmless if it isn't.

# --------------------------------------------------------------------------
# Configuration
# --------------------------------------------------------------------------

TOKEN = os.environ.get("DISCORD_TOKEN")
if not TOKEN:
    raise RuntimeError(
        "DISCORD_TOKEN environment variable is not set. Set it to your "
        "bot's token before starting the bot -- see README.md."
    )

# Optional: a guild (server) ID to sync commands to instantly while
# developing, instead of waiting up to an hour for a global sync.
DEV_GUILD_ID = os.environ.get("DEV_GUILD_ID")

# Where "undo" data for /unsilence is kept. Override with SILENCE_STATE_PATH
# if your host's writable disk isn't next to the script (e.g. a Docker
# volume) -- see README.md's deployment section.
STATE_FILE = Path(
    os.environ.get("SILENCE_STATE_PATH", str(Path(__file__).parent / "silence_state.json"))
)

# Permission required of the invoking member to run /silence or /unsilence.
# Change this, or override it per-role from Server Settings -> Integrations
# in Discord, to match how your server delegates voice moderation.
REQUIRED_PERMISSION = "mute_members"

# Role whose members /unverified lists. It's looked up by ID, not name, so
# renaming the role in Discord won't break the command.
UNVERIFIED_ROLE_ID = 1240357739625185360

# --- /tkl (verification) ---------------------------------------------------
# Only members who hold at least one of these roles may run /tkl. This list is the
# whole authorisation check; /tkl has no Discord-permission decorator on purpose.
TKL_STAFF_ROLE_IDS = (
    1240439873744277555,
    1240378485201965159,
    1240321970747478148,
)

# The role /tkl gives a verified member who is chosen for full access. (It takes away
# UNVERIFIED_ROLE_ID, above.)
KINGS_LEGION_ROLE_ID = 1240321873674244190

# The role /tkl gives instead, for a verified member chosen for limited (voice-channels-only)
# access. Also takes away UNVERIFIED_ROLE_ID; never given alongside KINGS_LEGION_ROLE_ID.
LIMITED_ACCESS_ROLE_ID = 1296591193261477982

# The channel the approval message sends new members to, to pick their roles.
ROLE_SELECTION_CHANNEL_ID = 1240330733411766302

# Where the timed mutes made with /mute are saved. This is a SEPARATE file from
# silence_state.json. On FadeHost set the MUTE_STATE_PATH environment variable to
# /data/timed_mutes.json so the records survive restarts and redeploys. If it is
# not set, /data is used when that folder exists; otherwise the file sits next to
# this script, which many hosts wipe on every deploy.
MUTE_STATE_FILE = Path(
    os.environ.get("MUTE_STATE_PATH")
    or (Path("/data/timed_mutes.json") if Path("/data").is_dir() else Path(__file__).parent / "timed_mutes.json")
)

# The text channel where every timed mute, expiry and early release is recorded.
# It is not a secret, so it lives here rather than in an environment variable.
MOD_LOG_CHANNEL_ID = 1240367306119450714

# --- /sos (Cyrodiil emergency alert) ----------------------------------------
# The role /sos pings. Looked up by ID, not name, so renaming it in Discord won't break the command.
# Discord-side, it's already set to "Allow anyone to @mention this role", which is what lets an
# ordinary member's /sos (using only the bot's own permissions) actually notify it.
SOS_ROLE_ID = 1241047163186708613

# How long the shared, server-wide /sos cooldown lasts after a successful announcement.
SOS_COOLDOWN = timedelta(minutes=30)

# The maximum length of a /sos reason. Same cap as /mute's, /ban's, and /kick's reason fields.
SOS_REASON_MAX = 300

# The banner image used on every /sos announcement embed. Not a secret, so it lives here.
SOS_BANNER_URL = (
    "https://media.discordapp.net/attachments/686253887216156694/1241212672113119252/"
    "Firefly_realistic_metal_shield_with_a_lion_in_blue_on_a_blue_war_banner_in_the_background_and_have_1.jpg"
)

# Where the one shared /sos cooldown (one UTC expiry timestamp per guild) is saved. Same /data
# fallback as MUTE_STATE_FILE, above, so it survives restarts and redeploys on FadeHost.
SOS_STATE_FILE = Path(
    os.environ.get("SOS_STATE_PATH")
    or (Path("/data/sos_state.json") if Path("/data").is_dir() else Path(__file__).parent / "sos_state.json")
)

# --- /limited (Limited Access member list) -----------------------------------
# The only channels /limited may be used in: the Officers channels. It posts a list of names for everyone
# in the channel to see, so it is kept to these channels. Anywhere else it gives the person a private
# refusal and shows nothing. Add or remove a channel ID here to change where it works.
# (The role it lists is LIMITED_ACCESS_ROLE_ID, above: the same one /tkl gives.)
OFFICER_CHANNEL_IDS = (
    1240356342863237151,
    1240356887220850848,
    1439765144510005408,
    1240367306119450714,
)

# --- ESO server-status observer ----------------------------------------------
# The ONE channel the observer posts to: a channel in the private test server. It is not a secret, so it lives
# here. The observer never posts anywhere else, and it refuses a channel that is in the same server as the
# mod-log channel above. Set this to 0 and it only writes to the log. Set the ESO_OBSERVER environment variable
# to "off" to stop the observer altogether, and ESO_OBSERVER_INTERVAL_SECONDS (60 to 3600) to change how
# often it looks at the page.
ESO_OBSERVER_CHANNEL_ID = 1072534493761642618
ESO_OBSERVER_PING_USER_ID = 662407182909964288  # Poss Bot @mentions this member when the observer posts a ⚠️ warning (0 = never ping)
ESO_OBSERVER_ENABLED = os.environ.get("ESO_OBSERVER", "on").strip().lower() not in ("off", "0", "false", "no")
try:
    ESO_OBSERVER_INTERVAL = min(3600, max(60, int(os.environ.get("ESO_OBSERVER_INTERVAL_SECONDS", "120"))))
except ValueError:
    ESO_OBSERVER_INTERVAL = 120

# --- ESO Xbox server status (the monitor, /server and /server-sim) ------------------------------------------
# All of this does nothing until the IDs below are filled in. Announcements go ONLY to the test channel until you decide to
# go live; the "main server" lines stay 0 until then. How to switch it on is explained in the section "ESO Xbox server
# status" further down this file. None of these IDs is a secret, so they live here rather than in environment variables.
ESO_STATUS_TEST_GUILD_ID = 686253887211962384  # The private test server's ID
ESO_STATUS_TEST_CHANNEL_ID = 1072534493761642618  # The test channel the announcements go to (the one the observer uses)
ESO_STATUS_MAIN_GUILD_ID = 1240321581792886795  # Leave 0 until the main-server rollout, then the main server's ID
ESO_STATUS_MAIN_CHANNEL_ID = 1240375898700517518  # Leave 0 until the main-server rollout, then the announcement channel's ID
NA_PING_ROLE_ID = 1561694223198191666  # Replace 0 with the Xbox NA notification role ID
EU_PING_ROLE_ID = 1561694258132422686  # Replace 0 with the Xbox EU notification role ID
ESO_STATUS_CATEGORY_ID = 1240321582434484317  # The category whose name shows a 🟢 or 🔴 for each Xbox megaserver (0 = leave it alone)

# The lengths /mute offers: (label shown in Discord, length in seconds).
MUTE_DURATIONS = (
    ("1 minute", 60),
    ("5 minutes", 300),
    ("10 minutes", 600),
    ("15 minutes", 900),
    ("30 minutes", 1800),
    ("1 hour", 3600),
    ("2 hours", 7200),
    ("6 hours", 21600),
    ("12 hours", 43200),
    ("24 hours", 86400),
)

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(name)s: %(message)s",
)
log = logging.getLogger("silence-bot")


# --------------------------------------------------------------------------
# Persistent "undo" state
#
# For each channel that's currently silenced via this bot, we remember just
# enough to put @everyone's Speak permission back exactly as it was:
#   - previous_speak: True (Allow) / False (Deny) / None (not set) -- the
#     value of the Speak field before /silence ran.
#   - had_overwrite: whether @everyone had ANY overwrite entry at all in
#     this channel before /silence touched it. If it didn't, and restoring
#     Speak leaves the overwrite fully empty again, /unsilence removes the
#     overwrite entry entirely instead of leaving a no-op one behind.
# --------------------------------------------------------------------------


class SilenceStore:
    def __init__(self, path: Path):
        self._path = path
        self._lock = asyncio.Lock()
        self._data: Dict[str, dict] = {}
        self._load()

    def _load(self) -> None:
        if self._path.exists():
            try:
                self._data = json.loads(self._path.read_text())
            except (json.JSONDecodeError, OSError):
                log.exception(
                    "Could not read %s; starting with empty silence state.", self._path
                )
                self._data = {}

    def _save(self) -> None:
        self._path.parent.mkdir(parents=True, exist_ok=True)
        self._path.write_text(json.dumps(self._data, indent=2))

    async def get(self, channel_id: int) -> Optional[dict]:
        async with self._lock:
            return self._data.get(str(channel_id))

    async def set(self, channel_id: int, previous_speak: Optional[bool], had_overwrite: bool) -> None:
        async with self._lock:
            self._data[str(channel_id)] = {
                "previous_speak": previous_speak,
                "had_overwrite": had_overwrite,
            }
            self._save()

    async def clear(self, channel_id: int) -> None:
        async with self._lock:
            if str(channel_id) in self._data:
                del self._data[str(channel_id)]
                self._save()


# --------------------------------------------------------------------------
# Timed mutes: saved records (used by /mute and /unmute)
#
# Every timed mute that is still running (or still needs attention) is one
# record in timed_mutes.json. This file is completely separate from
# silence_state.json. A record holds everything needed to finish the mute
# safely after a restart -- including the ABSOLUTE time it ends, never a
# countdown that could start again from zero.
#
#   status "applying" -> the record is saved just BEFORE Discord is asked to
#                        mute, so a crash can never leave a mute nobody is
#                        tracking.
#   status "active"   -> Discord confirmed the mute.
#   "release"         -> set when /unmute was used on someone who isn't in a
#                        voice channel (Discord only lets a bot unmute people
#                        who are connected), so it finishes when they rejoin.
#
# Finished mutes are deleted, so the file never grows into a history.
# --------------------------------------------------------------------------


def _utcnow() -> datetime:
    return datetime.now(timezone.utc)


def _iso(moment: datetime) -> str:
    return moment.astimezone(timezone.utc).replace(microsecond=0).isoformat()


def _parse_time(text: str) -> datetime:
    moment = datetime.fromisoformat(text)
    if moment.tzinfo is None:  # be forgiving if the file was edited by hand
        moment = moment.replace(tzinfo=timezone.utc)
    return moment.astimezone(timezone.utc)


def _fmt_time(moment: datetime) -> str:
    """An exact moment: Discord shows it in each reader's own time zone, and the
    UTC time is added so it is unambiguous in logs."""
    utc = moment.astimezone(timezone.utc)
    return f"<t:{int(utc.timestamp())}:F> ({utc:%Y-%m-%d %H:%M:%S} UTC)"


def _fmt_relative(moment: datetime) -> str:
    return f"<t:{int(moment.timestamp())}:R>"


def _fmt_end(moment: datetime) -> str:
    """How an end time is shown everywhere: exact moment, UTC, and 'in 10 minutes'."""
    return f"{_fmt_time(moment)} \u2014 {_fmt_relative(moment)}"


def _duration_label(seconds: int) -> str:
    for label, length in MUTE_DURATIONS:
        if length == seconds:
            return label
    minutes, rest = divmod(int(seconds), 60)
    return f"{minutes} minutes" if not rest else f"{seconds} seconds"


def _who(name: str, user_id: int) -> str:
    # Plain text, never a mention, so logs don't ping or link anyone.
    return f"{discord.utils.escape_markdown(name)} (`{user_id}`)"


def _key(guild_id: int, member_id: int) -> str:
    return f"{guild_id}:{member_id}"


def _outside_data_folder(path: Path, data_dir: Path = Path("/data")) -> bool:
    """True if this machine has a /data folder but the given file is not inside it (so it may not persist)."""
    try:
        return data_dir.is_dir() and data_dir.resolve() not in path.resolve().parents
    except (OSError, RuntimeError):  # RuntimeError: a symlink loop on older Pythons
        return False


def _clean_record(key: str, raw: Any) -> dict:
    """Check one record loaded from disk. Raises ValueError if it can't be trusted."""
    if not isinstance(raw, dict):
        raise ValueError("not an object")

    def need(name: str, kind: type) -> Any:
        value = raw.get(name)
        if isinstance(value, bool) or not isinstance(value, kind):
            raise ValueError(f"missing or invalid {name!r}")
        return value

    guild_id = need("guild_id", int)
    member_id = need("member_id", int)
    if key != _key(guild_id, member_id):
        raise ValueError("key does not match guild_id/member_id")
    duration = need("duration_seconds", int)
    if duration <= 0:
        raise ValueError("duration_seconds must be positive")
    case_id = need("id", str)
    if not case_id:
        raise ValueError("empty id")
    started_at = need("started_at", str)
    expires_at = need("expires_at", str)
    _parse_time(started_at)  # raises ValueError if unreadable
    _parse_time(expires_at)
    status = raw.get("status", "active")
    if status not in ("applying", "active"):
        raise ValueError("invalid status")
    reason = raw.get("reason")
    if reason is not None and not isinstance(reason, str):
        raise ValueError("invalid reason")
    release = raw.get("release")
    if release is not None:
        if not isinstance(release, dict) or isinstance(release.get("by_id"), bool) or not isinstance(release.get("by_id"), int):
            raise ValueError("invalid release")
        release = {"by_id": release["by_id"], "by_name": str(release.get("by_name") or "Unknown")}
    return {
        "id": case_id,
        "status": status,
        "guild_id": guild_id,
        "member_id": member_id,
        "member_name": str(raw.get("member_name") or "Unknown member"),
        "moderator_id": need("moderator_id", int),
        "moderator_name": str(raw.get("moderator_name") or "Unknown moderator"),
        "started_at": started_at,
        "expires_at": expires_at,
        "duration_seconds": duration,
        "reason": reason,
        "release": release,
    }


class MuteStore:
    """Loads and saves timed_mutes.json. Knows nothing about Discord."""

    def __init__(self, path: Path):
        self._path = path
        self._lock: Optional[asyncio.Lock] = None  # created on first use, inside the running event loop
        self._unsafe = False  # True if an unreadable file could not be moved aside
        self.problems: List[str] = []  # notes about anything odd found while loading
        self.records: Dict[str, dict] = self._load()

    @property
    def path(self) -> Path:
        return self._path

    def _set_aside(self, label: str, keep_original: bool = False) -> Optional[Path]:
        """Keep a copy of the file under another name so nothing recoverable is lost."""
        stamp = _utcnow().strftime("%Y%m%dT%H%M%SZ")
        target = self._path.with_name(f"{self._path.name}.{label}-{stamp}")
        try:
            if keep_original:
                shutil.copy2(self._path, target)
            else:
                os.replace(self._path, target)
            return target
        except OSError:
            log.exception("Could not set aside %s", self._path)
            return None

    def _load(self) -> Dict[str, dict]:
        try:
            text = self._path.read_text(encoding="utf-8")
        except FileNotFoundError:
            return {}  # first run: start empty
        except OSError as exc:
            return self._unusable(exc)
        try:
            data = json.loads(text)
            raw = data["mutes"]
            if not isinstance(raw, dict):
                raise ValueError("'mutes' is not an object")
        except (ValueError, KeyError, TypeError) as exc:
            return self._unusable(exc)

        records: Dict[str, dict] = {}
        skipped = 0
        for key, entry in raw.items():
            try:
                records[key] = _clean_record(key, entry)
            except ValueError as exc:
                skipped += 1
                log.error("Skipping invalid timed-mute record %r (%s): %r", key, exc, entry)
        if skipped:
            copy = self._set_aside("invalid", keep_original=True)
            self.problems.append(
                f"{skipped} saved timed-mute record(s) were invalid and were skipped"
                + (f"; the original file was kept as `{copy.name}`." if copy else ".")
                + " Check voice channels for anyone who is still server-muted."
            )
        return records

    def _unusable(self, exc: BaseException) -> Dict[str, dict]:
        """The file exists but can't be read. Never overwrite it: move it aside first."""
        log.error("Timed-mute file %s is unreadable (%s).", self._path, exc)
        saved = self._set_aside("corrupt")
        if saved is None:
            self._unsafe = True  # refuse to write, so the damaged file can't be overwritten
            self.problems.append(
                "The saved timed-mute file is unreadable and could not be moved aside, so new "
                "timed mutes are disabled until it is fixed. Check voice channels for anyone "
                "who is still server-muted."
            )
        else:
            self.problems.append(
                f"The saved timed-mute file was unreadable. It was kept as `{saved.name}` and "
                "Poss Bot started with no saved mutes. Check voice channels for anyone who "
                "is still server-muted."
            )
        return {}

    async def save(self, records: Dict[str, dict]) -> None:
        """Write all records atomically. Raises OSError if the file can't be written."""
        if self._lock is None:
            self._lock = asyncio.Lock()
        async with self._lock:
            if self._unsafe:
                raise OSError("timed-mute file is unreadable and was not moved aside; refusing to overwrite it")
            text = json.dumps({"version": 1, "mutes": records}, indent=2, sort_keys=True)
            self._path.parent.mkdir(parents=True, exist_ok=True)
            temp = self._path.with_name(self._path.name + ".tmp")
            with open(temp, "w", encoding="utf-8") as handle:
                handle.write(text)
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temp, self._path)  # all-or-nothing swap


# --------------------------------------------------------------------------
# Timed mutes: the manager
#
# One asynchronous expiry task per running mute (no polling), a lock per
# member so /mute, /unmute, automatic expiry and voice events for the same
# person can never run at the same time, and a single routine (_resolve) that
# decides what a mute needs next. Startup recovery, expiry and /unmute all go
# through that routine, so they behave consistently.
# --------------------------------------------------------------------------

# What _resolve() tells its caller to do next.
_DONE = "done"              # the mute was finished and its record removed
_NOT_YET = "not_yet"        # still running: wait for the scheduled end
_WAIT_VOICE = "wait_voice"  # due, but the member isn't in voice: finish when they rejoin
_RETRY = "retry"            # a Discord or data problem right now: try again later

_RETRY_DELAYS = (30, 60, 120, 300, 600, 900)  # seconds between retries; the last one repeats
_MAX_SLEEP = 3600           # while waiting, check the real clock at least hourly
_GUILD_GONE_AFTER = 8       # give up on a record after this many attempts with the server missing
_SEND_TIMEOUT = 15          # seconds to wait for a DM or log message before giving up

# Moderation-log entries: (title, embed colour, explanation).
_LOG_KINDS = {
    "started": ("\U0001F507 Timed mute started", 0xE67E22, None),
    "unmuted_expired": (
        "\U0001F50A Timed mute expired", 0x2ECC71,
        "The mute reached its scheduled end and the member was unmuted.",
    ),
    "unmuted_released": (
        "\U0001F50A Timed mute released early", 0x3498DB,
        "The mute was ended early with /unmute and the member was unmuted.",
    ),
    "manual_unmute": (
        "\U0001F50A Timed mute ended early in Discord", 0x9B59B6,
        "The member was unmuted directly in Discord (not with /unmute), so the timer was cancelled.",
    ),
    "already_unmuted_expired": (
        "✅ Timed mute had already ended", 0x95A5A6,
        "The scheduled end was reached and the member was already unmuted, so nothing needed changing.",
    ),
    "already_unmuted_early": (
        "✅ Timed mute ended before its scheduled time", 0x95A5A6,
        "The member was found unmuted before the scheduled end. It was ended outside Poss Bot "
        "while Poss Bot wasn't watching, so the timer was cancelled.",
    ),
    "left_guild": (
        "⚠️ Timed mute record removed: member left", 0xF1C40F,
        "The member is no longer in the server, so there was nothing to unmute and the record was removed.",
    ),
    "never_applied": (
        "⚠️ Unconfirmed timed mute discarded", 0xF1C40F,
        "Discord never confirmed this mute and the member is not muted, so the record was discarded.",
    ),
    "guild_gone": (
        "⚠️ Timed mute record dropped", 0xF1C40F,
        "Poss Bot is no longer in this server, so the mute could not be finished and the record was dropped.",
    ),
    "waiting_expired": (
        "⏳ Timed mute is waiting for the member to join voice", 0xF1C40F,
        "The time is up, but Discord only lets a bot unmute someone who is connected to a voice channel. "
        "The member will be unmuted automatically as soon as they next join one.",
    ),
    "waiting_release": (
        "⏳ Early release is waiting for the member to join voice", 0xF1C40F,
        "An early release was requested, but Discord only lets a bot unmute someone who is connected to a "
        "voice channel. The member will be unmuted automatically as soon as they next join one.",
    ),
    "unmute_failed": (
        "⚠️ Couldn't lift a timed mute", 0xE74C3C,
        "Discord wouldn't let Poss Bot unmute this member.",
    ),
}

_TRIGGER_NOTES = {
    "startup": "Found while Poss Bot was starting up.",
    "rejoin": "Completed when the member next joined a voice channel.",
}


class MuteResult:
    """What /mute needs to tell the moderator."""

    def __init__(self) -> None:
        self.error: Optional[str] = None  # set when the member was not (confirmed) muted
        self.record: Optional[dict] = None
        self.dm_sent = False
        self.logged = False
        self.saved = True


class MuteManager:
    def __init__(self, bot: commands.Bot, store: MuteStore):
        self.bot = bot
        self._store = store
        self._records: Dict[str, dict] = store.records
        self._tasks: Dict[str, asyncio.Task] = {}  # the single expiry task of each running mute
        self._locks: Dict[str, list] = {}  # member key -> [lock, number of users]
        self._alerted: Set[str] = set()  # case ids we have already posted a warning for
        self._misses: Dict[str, int] = {}  # member key -> times the server was unavailable
        self._notices: List[str] = list(store.problems)  # file problems to report once logging works
        self._reconciling = False

    # ----- small building blocks ------------------------------------------

    @contextlib.asynccontextmanager
    async def _member_lock(self, key: str):
        """One lock per member. It is removed again as soon as nobody is using it."""
        entry = self._locks.get(key)
        if entry is None:
            entry = self._locks[key] = [asyncio.Lock(), 0]
        entry[1] += 1
        try:
            async with entry[0]:
                yield
        finally:
            entry[1] -= 1
            if entry[1] == 0:
                self._locks.pop(key, None)

    async def _persist(self) -> bool:
        try:
            await self._store.save(self._records)
            return True
        except Exception:
            log.exception("Could not save the timed-mute records")
            return False

    def _cancel_task(self, key: str) -> None:
        task = self._tasks.pop(key, None)
        if task is not None and task is not asyncio.current_task() and not task.done():
            task.cancel()

    def _schedule(self, key: str, case_id: str) -> None:
        """Make sure exactly one expiry task exists for this mute."""
        self._cancel_task(key)
        task = asyncio.create_task(self._expiry_task(key, case_id), name=f"timed-mute-{case_id}")
        self._tasks[key] = task

        def forget(finished: asyncio.Task, key: str = key) -> None:
            if self._tasks.get(key) is finished:
                del self._tasks[key]

        task.add_done_callback(forget)

    def _ensure_task(self, key: str, case_id: str) -> None:
        task = self._tasks.get(key)
        if task is None or task.done():
            self._schedule(key, case_id)

    async def _log_channel(self, guild_id: Optional[int]) -> Tuple[Optional[discord.TextChannel], str]:
        """The moderation-log channel if it can be used right now, otherwise (None, why not)."""
        channel = self.bot.get_channel(MOD_LOG_CHANNEL_ID)
        if channel is None:
            try:
                channel = await self.bot.fetch_channel(MOD_LOG_CHANNEL_ID)
            except discord.NotFound:
                return None, "the channel no longer exists"
            except discord.Forbidden:
                return None, "I don't have access to it"
            except discord.HTTPException:
                return None, "Discord didn't answer when I looked it up"
        if not isinstance(channel, discord.TextChannel):
            return None, "it isn't a text channel"
        channel_guild = channel.guild
        if guild_id is not None and getattr(channel_guild, "id", None) != guild_id:
            return None, "it belongs to a different server"
        me = getattr(channel_guild, "me", None)  # a bare placeholder server (not in the cache) has no .me
        if me is None:
            return None, "I couldn't check my permissions there"
        permissions = channel.permissions_for(me)
        missing = [
            label
            for flag, label in (
                ("view_channel", "View Channel"),
                ("send_messages", "Send Messages"),
                ("embed_links", "Embed Links"),
            )
            if not getattr(permissions, flag)
        ]
        if missing:
            return None, "I'm missing permissions there: " + ", ".join(missing)
        return channel, ""

    def _embed(
        self, kind: str, record: dict, *, by: Optional[str] = None,
        dm: Optional[str] = None, context: Optional[str] = None,
    ) -> discord.Embed:
        title, colour, explanation = _LOG_KINDS[kind]
        description = " ".join(part for part in (explanation, context) if part) or None
        embed = discord.Embed(title=title, description=description, colour=discord.Colour(colour))
        expires = _parse_time(record["expires_at"])
        embed.add_field(name="Member", value=_who(record["member_name"], record["member_id"]), inline=True)
        embed.add_field(name="Set by", value=_who(record["moderator_name"], record["moderator_id"]), inline=True)
        if by:
            embed.add_field(name="Released by", value=by, inline=True)
        embed.add_field(name="Duration", value=_duration_label(record["duration_seconds"]), inline=True)
        if kind == "started":
            embed.add_field(name="Started", value=_fmt_time(_parse_time(record["started_at"])), inline=False)
        embed.add_field(name="Scheduled end", value=_fmt_end(expires), inline=False)
        if kind == "started":
            embed.add_field(name="Reason", value=record["reason"] or "No reason provided", inline=False)
        if dm is not None:
            embed.add_field(name="DM to member", value=dm, inline=False)
        embed.set_footer(text=f"Case {record['id']}")
        embed.timestamp = _utcnow()
        return embed

    async def _send_log(
        self, kind: str, record: dict, *, by: Optional[str] = None,
        dm: Optional[str] = None, context: Optional[str] = None,
    ) -> bool:
        """Post one moderation-log entry. Never raises; returns False if it couldn't be posted."""
        try:
            channel, problem = await self._log_channel(record["guild_id"])
            if channel is None:
                log.error("Case %s: moderation log unavailable (%s); could not post %r", record["id"], problem, kind)
                return False
            await asyncio.wait_for(
                channel.send(
                    embed=self._embed(kind, record, by=by, dm=dm, context=context),
                    allowed_mentions=discord.AllowedMentions.none(),
                ),
                timeout=_SEND_TIMEOUT,
            )
            return True
        except Exception:
            log.exception("Case %s: could not post %r to the moderation log", record["id"], kind)
            return False

    async def _send_dm(self, member: discord.Member, guild: discord.Guild, record: dict) -> bool:
        """Tell the member about their mute (once). A failure never cancels the mute."""
        expires = _parse_time(record["expires_at"])
        text = (
            f"You have been server-muted in **{discord.utils.escape_markdown(guild.name)}** "
            f"for **{_duration_label(record['duration_seconds'])}**.\n"
            f"Reason: {record['reason'] or 'No reason provided'}\n"
            f"Ends: {_fmt_end(expires)}\n"
            "It will be lifted automatically."
        )
        try:
            await asyncio.wait_for(
                member.send(text, allowed_mentions=discord.AllowedMentions.none()), timeout=_SEND_TIMEOUT
            )
            return True
        except discord.Forbidden:
            log.info("Case %s: the member has DMs closed or has blocked the bot", record["id"])
        except Exception:
            log.exception("Case %s: could not DM the member", record["id"])
        return False

    async def _alert_once(self, kind: str, record: dict, context: Optional[str] = None) -> None:
        """A warning in the moderation log, posted once per mute so it can't spam."""
        if record["id"] in self._alerted:
            return
        self._alerted.add(record["id"])
        release = record.get("release")
        by = _who(release["by_name"], release["by_id"]) if release and kind == "waiting_release" else None
        await self._send_log(kind, record, by=by, context=context)

    async def _conclude(self, key: str, record: dict, outcome: str, trigger: str) -> None:
        """Finish a mute: remove its record and timer, then write the one log entry."""
        self._records.pop(key, None)
        self._cancel_task(key)
        self._alerted.discard(record["id"])
        self._misses.pop(key, None)
        if not await self._persist():
            log.error(
                "Case %s: finished, but the saved records could not be updated. "
                "The leftover record is cleaned up on the next start.", record["id"],
            )
        log.info("Case %s (%s): %s [%s]", record["id"], key, outcome, trigger)
        release = record.get("release")
        by = _who(release["by_name"], release["by_id"]) if release and outcome == "unmuted_released" else None
        await self._send_log(outcome, record, by=by, context=_TRIGGER_NOTES.get(trigger))

    # ----- deciding what a mute needs next --------------------------------

    async def _resolve(self, key: str, case_id: str, trigger: str) -> Tuple[str, Optional[str]]:
        """Look at one mute and do whatever it needs now. The caller must hold the member's lock.

        Returns (what_next, outcome); outcome names how a finished mute ended.
        trigger says why we're looking: "expiry", "startup", "unmute", "rejoin" or "voice".
        """
        record = self._records.get(key)
        if record is None or record["id"] != case_id:
            return _DONE, "superseded"  # already finished, or replaced by a newer mute

        guild = self.bot.get_guild(record["guild_id"])
        if guild is None or guild.unavailable:
            misses = self._misses[key] = self._misses.get(key, 0) + 1
            if guild is None and misses >= _GUILD_GONE_AFTER:
                log.error("Case %s: Poss Bot is no longer in server %s; dropping the record.", case_id, record["guild_id"])
                await self._conclude(key, record, "guild_gone", trigger)
                return _DONE, "guild_gone"
            log.warning("Case %s: server %s isn't available right now; will try again.", case_id, record["guild_id"])
            return _RETRY, None
        self._misses.pop(key, None)

        member = guild.get_member(record["member_id"])
        if member is None:
            try:
                member = await guild.fetch_member(record["member_id"])
            except discord.NotFound:
                await self._conclude(key, record, "left_guild", trigger)
                return _DONE, "left_guild"
            except discord.HTTPException:
                log.warning("Case %s: couldn't look up the member right now; will try again.", case_id)
                return _RETRY, None

        time_up = _utcnow() >= _parse_time(record["expires_at"])
        release = record.get("release")
        due = time_up or release is not None
        voice = member.voice

        if voice is None or voice.channel is None:
            # Discord only lets a bot change a mute while the member is connected.
            if not due:
                return _NOT_YET, None
            await self._alert_once("waiting_release" if release else "waiting_expired", record)
            return _WAIT_VOICE, None

        if not voice.mute:
            # Not muted any more: never touch them, just tidy up.
            if record["status"] == "applying":
                outcome = "never_applied"
            elif time_up:
                outcome = "already_unmuted_expired"
            else:
                outcome = "already_unmuted_early"
            await self._conclude(key, record, outcome, trigger)
            return _DONE, outcome

        if record["status"] == "applying":  # Discord did mute them after all: keep tracking it
            record["status"] = "active"
            await self._persist()
        if not due:
            return _NOT_YET, None

        reason = f"Timed mute released early by {release['by_name']}" if release else "Timed mute expired"
        try:
            await member.edit(mute=False, reason=reason)
        except discord.NotFound:
            await self._conclude(key, record, "left_guild", trigger)
            return _DONE, "left_guild"
        except discord.HTTPException as exc:
            if exc.code == 40032:  # they left voice a moment ago
                await self._alert_once("waiting_release" if release else "waiting_expired", record)
                return _WAIT_VOICE, None
            log.error("Case %s: Discord refused the unmute (HTTP %s, code %s)", case_id, exc.status, exc.code)
            await self._unmute_failed(record, trigger, "I don't have permission to unmute them." if exc.status == 403
                                      else f"Discord returned an error ({exc.status}).")
            return _RETRY, None
        except Exception:
            log.exception("Case %s: unexpected error while unmuting", case_id)
            await self._unmute_failed(record, trigger, "An unexpected error happened (details are in the bot's logs).")
            return _RETRY, None

        outcome = "unmuted_released" if release else "unmuted_expired"
        await self._conclude(key, record, outcome, trigger)
        return _DONE, outcome

    async def _unmute_failed(self, record: dict, trigger: str, why: str) -> None:
        if trigger != "unmute":  # /unmute reports the failure straight to the moderator instead
            await self._alert_once(
                "unmute_failed", record,
                f"{why} Poss Bot will keep retrying; you can also unmute them yourself in Discord.",
            )

    async def _expiry_task(self, key: str, case_id: str) -> None:
        """Sleeps until the saved end time, then finishes the mute. One task per mute.

        It re-reads the real clock after every sleep, retries with a growing delay if
        Discord fails, and exits as soon as its record is gone or has been replaced.
        """
        await self.bot.wait_until_ready()
        attempt = 0
        while True:
            record = self._records.get(key)
            if record is None or record["id"] != case_id:
                return
            remaining = (_parse_time(record["expires_at"]) - _utcnow()).total_seconds()
            if remaining > 0 and record.get("release") is None:
                await asyncio.sleep(min(remaining, _MAX_SLEEP))
                continue
            try:
                async with self._member_lock(key):
                    step, _ = await self._resolve(key, case_id, "expiry")
            except Exception:
                log.exception("Case %s: unexpected error while ending a timed mute", case_id)
                step = _RETRY
            if step in (_DONE, _WAIT_VOICE):
                return  # WAIT_VOICE is finished by the voice listener when they rejoin
            if step == _NOT_YET:  # only if the clock moved; look again shortly, never spin
                await asyncio.sleep(1)
                continue
            await asyncio.sleep(_RETRY_DELAYS[min(attempt, len(_RETRY_DELAYS) - 1)])
            attempt += 1

    # ----- /mute ------------------------------------------------------------

    async def start_mute(
        self, guild: discord.Guild, target: discord.abc.User, moderator: discord.Member,
        seconds: int, reason: Optional[str],
    ) -> MuteResult:
        result = MuteResult()
        member = guild.get_member(target.id) or (target if isinstance(target, discord.Member) else None)
        if member is None:
            result.error = "That user isn’t a member of this server."
            return result
        key = _key(guild.id, member.id)

        async with self._member_lock(key):
            voice = member.voice
            if voice is None or voice.channel is None:
                result.error = "That user isn’t in a voice channel."
                return result
            if voice.mute:
                result.error = "That user is already server-muted."
                if key in self._records:
                    result.error += " Poss Bot is already timing that mute; use /unmute to end it early."
                return result
            me = guild.me
            if me is None or not voice.channel.permissions_for(me).mute_members:
                result.error = (
                    "I don't have the **Mute Members** permission in that voice channel, "
                    "so I can't server-mute anyone there."
                )
                return result
            channel, problem = await self._log_channel(guild.id)
            if channel is None:
                result.error = (
                    f"I can't use the moderation-log channel ({problem}), so I haven't muted anyone. "
                    "Please ask an admin to check it."
                )
                return result

            old = self._records.get(key)
            if old is not None:  # they aren't muted, so an older record can only be stale
                await self._conclude(
                    key, old, "never_applied" if old["status"] == "applying" else "already_unmuted_early", "mute"
                )

            now = _utcnow()
            started = now.replace(microsecond=0)
            ends = now + timedelta(seconds=seconds)
            if ends.microsecond:  # round UP to a whole second so the time shown IS the real end
                ends = (ends + timedelta(seconds=1)).replace(microsecond=0)
            record = {
                "id": secrets.token_hex(4),
                "status": "applying",
                "guild_id": guild.id,
                "member_id": member.id,
                "member_name": member.display_name,
                "moderator_id": moderator.id,
                "moderator_name": moderator.display_name,
                "started_at": _iso(started),
                "expires_at": _iso(ends),
                "duration_seconds": seconds,
                "reason": reason,
                "release": None,
            }
            # Save first, mute second: if the bot dies in between, the record is still there.
            self._records[key] = record
            if not await self._persist():
                self._records.pop(key, None)
                result.error = (
                    "I couldn't save the mute record (a storage problem), so I haven't muted anyone. "
                    "The details are in the bot's logs."
                )
                return result

            audit_reason = f"Timed mute ({_duration_label(seconds)}) by {moderator}: {reason or 'No reason provided'}"
            try:
                await member.edit(mute=True, reason=audit_reason[:500])
            except discord.Forbidden:
                await self._forget(key)
                result.error = (
                    "Discord wouldn't let me server-mute that user (I may be missing the **Mute Members** "
                    "permission). Nobody has been muted."
                )
                return result
            except discord.NotFound:
                await self._forget(key)
                result.error = "That user is no longer in the server."
                return result
            except discord.HTTPException as exc:
                if exc.code == 40032:
                    await self._forget(key)
                    result.error = "That user isn’t in a voice channel any more."
                    return result
                if exc.status < 500:
                    await self._forget(key)
                    result.error = f"Discord rejected the mute (error {exc.status}), so nobody has been muted."
                    return result
                log.exception("Case %s: the mute request failed and its outcome is unknown", record["id"])
                result.error = self._unconfirmed_message()
                return result
            except Exception:
                log.exception("Case %s: the mute request failed and its outcome is unknown", record["id"])
                result.error = self._unconfirmed_message()
                return result

            record["status"] = "active"
            result.saved = await self._persist()
            if not result.saved:
                log.error("Case %s: muted, but the 'active' update could not be saved", record["id"])
            self._schedule(key, record["id"])
            result.record = record
            result.dm_sent = await self._send_dm(member, guild, record)
            result.logged = await self._send_log(
                "started", record,
                dm="Delivered" if result.dm_sent else "Could not be delivered (DMs closed or bot blocked)",
            )
            return result

    @staticmethod
    def _unconfirmed_message() -> str:
        return (
            "Discord didn't confirm the mute (it returned an error or timed out). If that user now shows "
            "as server-muted, Poss Bot will notice and keep track of it; if not, nothing happened. "
            "Check the bot's logs if you're unsure."
        )

    async def _forget(self, key: str) -> None:
        """Drop a record whose mute definitely never happened."""
        self._records.pop(key, None)
        if not await self._persist():
            log.error("Could not save the removal of a mute that never happened (%s)", key)

    # ----- /unmute ----------------------------------------------------------

    async def stop_mute(self, guild: discord.Guild, member_id: int, moderator: discord.Member) -> str:
        """End a Poss Bot timed mute early. Returns the private reply for the moderator."""
        key = _key(guild.id, member_id)
        async with self._member_lock(key):
            record = self._records.get(key)
            if record is None:
                return (
                    "There is no active timed mute tracked by Poss Bot for that member, so I haven't changed "
                    "anything. (If someone else server-muted them, unmute them in Discord yourself.)"
                )
            name = discord.utils.escape_markdown(record["member_name"])
            previous = record.get("release")
            record["release"] = {"by_id": moderator.id, "by_name": moderator.display_name}
            step, outcome = await self._resolve(key, record["id"], "unmute")

            if step == _DONE:
                if outcome == "unmuted_released":
                    return f"\U0001F50A Unmuted **{name}**. Their timed mute has been ended early."
                if outcome == "left_guild":
                    return f"**{name}** is no longer in the server, so there was nothing to unmute. I removed the record."
                if outcome == "never_applied":
                    return f"**{name}** isn't muted, and the mute was never confirmed. I discarded the record."
                if outcome in ("already_unmuted_expired", "already_unmuted_early"):
                    return f"**{name}** was already unmuted, so there was nothing to undo. I cleaned up the old record."
                return f"The timed mute for **{name}** had already finished, so there was nothing to do."
            if step == _WAIT_VOICE:
                await self._persist()  # keep the release request so it survives a restart
                return (
                    f"**{name}** isn’t in a voice channel right now, and Discord only lets me unmute people "
                    "who are connected. Their mute will be lifted automatically as soon as they next join one."
                )
            # Couldn't do it right now: put the record back exactly as it was.
            record["release"] = previous
            return (
                f"I couldn't unmute **{name}** just now (Discord returned an error or I'm missing the "
                "**Mute Members** permission). Their timed mute is still being tracked. "
                "Please try again, or unmute them in Discord yourself."
            )

    # ----- events -----------------------------------------------------------

    async def on_voice_update(
        self, member: discord.Member, before: discord.VoiceState, after: discord.VoiceState
    ) -> None:
        key = _key(member.guild.id, member.id)
        if key not in self._records:
            return  # not one of ours: nothing to do
        unmuted_while_connected = before.mute and not after.mute and after.channel is not None
        joined_voice = before.channel is None and after.channel is not None
        became_muted = not before.mute and after.mute
        if not (unmuted_while_connected or joined_voice or became_muted):
            return

        # Poss Bot's own mute and unmute calls hold this same lock while they run, so by the time
        # we get it the record is either gone (Poss Bot did it) or still here (someone else did).
        async with self._member_lock(key):
            record = self._records.get(key)
            if record is None:
                return
            if unmuted_while_connected and record["status"] == "active":
                current = member.voice
                if current is not None and current.mute:
                    return  # an out-of-date event: they are muted again
                await self._conclude(key, record, "manual_unmute", "voice")
                return
            step, _ = await self._resolve(key, record["id"], "rejoin" if joined_voice else "voice")
            if step in (_NOT_YET, _RETRY):
                self._ensure_task(key, record["id"])

    async def on_member_remove(self, member: discord.Member) -> None:
        key = _key(member.guild.id, member.id)
        if key not in self._records:
            return
        async with self._member_lock(key):
            record = self._records.get(key)
            if record is not None:
                await self._conclude(key, record, "left_guild", "member_remove")

    async def on_ready(self) -> None:
        path = self._store.path
        log.info("Timed-mute records are stored in %s", path)
        if _outside_data_folder(path):
            log.warning(
                "The timed-mute file is not inside /data, so it may be lost when the host redeploys. "
                "Set the MUTE_STATE_PATH environment variable to /data/timed_mutes.json."
            )
        if not path.exists():  # first run: create it now so a storage problem shows up at startup, not at the first /mute
            if await self._persist():
                log.info("Created an empty timed-mute file.")
            else:
                log.error("Poss Bot cannot write to the timed-mute file, so /mute is refused until that is fixed.")
        channel, problem = await self._log_channel(None)
        if channel is None:
            log.error(
                "Moderation-log channel %s is not usable (%s): /mute is refused until this is fixed.",
                MOD_LOG_CHANNEL_ID, problem,
            )
        elif self._notices:
            notices, self._notices = self._notices, []
            for notice in notices:
                try:
                    await channel.send(f"⚠️ {notice}", allowed_mentions=discord.AllowedMentions.none())
                except Exception:
                    log.exception("Could not post a timed-mute file notice to the moderation log")
        await self.reconcile_all()

    async def reconcile_all(self) -> None:
        """Check every saved mute against what Discord reports right now (runs at every ready)."""
        if self._reconciling:
            return
        self._reconciling = True
        try:
            keys = list(self._records)
            if keys:
                log.info("Checking %d saved timed mute(s) against the current server state", len(keys))
            for key in keys:
                record = self._records.get(key)
                if record is None:
                    continue
                try:
                    async with self._member_lock(key):
                        step, _ = await self._resolve(key, record["id"], "startup")
                except Exception:
                    log.exception("Case %s: unexpected error while checking a saved timed mute", record["id"])
                    step = _RETRY
                if step in (_NOT_YET, _RETRY):
                    self._ensure_task(key, record["id"])
        finally:
            self._reconciling = False


# /sos's cooldown store and manager are defined here, next to MuteStore/MuteManager above, rather
# than down with the rest of /sos near the end of the file -- because SilenceBot.__init__, just
# below, constructs one of each, and that has to happen after the class exists.
class SosStore:
    """Loads and saves sos_state.json: one shared cooldown expiry per guild. Knows nothing about Discord."""

    def __init__(self, path: Path):
        self._path = path
        self._lock: Optional[asyncio.Lock] = None  # created on first use, inside the running event loop
        self._unsafe = False  # True if an unreadable file could not be moved aside
        self.problems: List[str] = []  # notes about anything odd found while loading
        self.expiries: Dict[str, str] = self._load()  # guild id (str) -> ISO 8601 UTC expiry

    def _set_aside(self, label: str) -> Optional[Path]:
        """Keep the broken file under another name so nothing recoverable is lost."""
        stamp = _utcnow().strftime("%Y%m%dT%H%M%SZ")
        target = self._path.with_name(f"{self._path.name}.{label}-{stamp}")
        try:
            os.replace(self._path, target)
            return target
        except OSError:
            log.exception("Could not set aside %s", self._path)
            return None

    def _load(self) -> Dict[str, str]:
        try:
            text = self._path.read_text(encoding="utf-8")
        except FileNotFoundError:
            return {}  # first run: nobody is on cooldown yet
        except OSError as exc:
            log.error("/sos state file %s is unreadable (%s).", self._path, exc)
            self._unsafe = True  # refuse to write, so the damaged file can't be overwritten
            self.problems.append(
                "The saved /sos cooldown file couldn’t be read, so /sos is starting with no cooldown "
                "saved for any server, and new cooldowns can’t be saved until it’s fixed."
            )
            return {}

        try:
            data = json.loads(text)
            raw = data["cooldowns"]
            if not isinstance(raw, dict):
                raise ValueError("'cooldowns' is not an object")
        except (ValueError, KeyError, TypeError) as exc:
            log.error("/sos state file %s is malformed (%s).", self._path, exc)
            saved = self._set_aside("corrupt")
            self.problems.append(
                "The saved /sos cooldown file was malformed."
                + (f" It was kept as `{saved.name}`." if saved else "")
                + " /sos is starting with no cooldown saved for any server."
            )
            return {}

        cleaned: Dict[str, str] = {}
        skipped = 0
        for key, value in raw.items():
            try:
                if not (isinstance(key, str) and key.isdigit()):
                    raise ValueError("not a guild id")
                _parse_time(value)  # just to validate the timestamp; the original string is what's kept
            except Exception:
                skipped += 1
                continue
            cleaned[key] = value
        if skipped:
            log.warning("/sos: skipped %d invalid cooldown record(s) in %s", skipped, self._path)
            self.problems.append(f"{skipped} saved /sos cooldown record(s) were invalid and were skipped.")
        return cleaned

    async def save(self, expiries: Dict[str, str]) -> None:
        """Write every guild's cooldown atomically. Raises OSError if the file can't be written."""
        if self._lock is None:
            self._lock = asyncio.Lock()
        async with self._lock:
            if self._unsafe:
                raise OSError("/sos state file is unreadable and was not moved aside; refusing to overwrite it")
            text = json.dumps({"version": 1, "cooldowns": expiries}, indent=2, sort_keys=True)
            self._path.parent.mkdir(parents=True, exist_ok=True)
            temp = self._path.with_name(self._path.name + ".tmp")
            with open(temp, "w", encoding="utf-8") as handle:
                handle.write(text)
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temp, self._path)  # all-or-nothing swap


class SosManager:
    """The one shared, persisted /sos cooldown per guild, and the lock that keeps checking it and
    starting a new one from ever racing."""

    def __init__(self, store: SosStore):
        self._store = store
        self._expiries: Dict[str, str] = store.expiries  # guild id (str) -> ISO 8601 UTC expiry
        self._locks: Dict[int, list] = {}  # guild id -> [lock, number of users]

    @contextlib.asynccontextmanager
    async def lock(self, guild_id: int):
        """One lock per guild: hold this for the whole check-then-send-then-start sequence so two
        /sos calls arriving at almost the same moment can't both get through."""
        entry = self._locks.get(guild_id)
        if entry is None:
            entry = self._locks[guild_id] = [asyncio.Lock(), 0]
        entry[1] += 1
        try:
            async with entry[0]:
                yield
        finally:
            entry[1] -= 1
            if entry[1] == 0:
                self._locks.pop(guild_id, None)

    def active_until(self, guild_id: int) -> Optional[datetime]:
        """This guild's current /sos cooldown expiry, or None if /sos is available right now.
        Call this only while holding lock(guild_id)."""
        text = self._expiries.get(str(guild_id))
        if text is None:
            return None
        try:
            expires = _parse_time(text)
        except ValueError:
            return None  # a corrupted single entry: treat it as no cooldown rather than jamming /sos forever
        return expires if expires > _utcnow() else None

    async def start(self, guild_id: int) -> None:
        """Start a fresh cooldown for this guild right now, and save it. Only call this after the
        announcement has actually been sent, while still holding lock(guild_id)."""
        expires = _utcnow() + SOS_COOLDOWN
        self._expiries[str(guild_id)] = _iso(expires)
        try:
            await self._store.save(dict(self._expiries))
        except Exception:
            log.exception("/sos: could not save the new cooldown for guild %s", guild_id)
            # The cooldown still applies for the rest of this run -- it's already in self._expiries,
            # above -- so nobody can double-dip; only a restart before the next successful save would
            # lose it early.


# --------------------------------------------------------------------------
# Bot setup
# --------------------------------------------------------------------------

intents = discord.Intents.default()
intents.voice_states = True  # Needed so Member.voice is populated.
# PRIVILEGED INTENT: /unverified needs the full member list to see who holds
# the Unverified role. "Server Members Intent" must ALSO be switched on under
# Bot -> Privileged Gateway Intents in the Discord Developer Portal, or the
# bot will refuse to start.
intents.members = True


class SilenceBot(commands.Bot):
    def __init__(self):
        super().__init__(command_prefix="!", intents=intents)
        self.store = SilenceStore(STATE_FILE)
        self.mutes = MuteManager(self, MuteStore(MUTE_STATE_FILE))  # timed mutes: /mute and /unmute
        self.sos = SosManager(SosStore(SOS_STATE_FILE))  # the shared /sos cooldown

    async def setup_hook(self):
        if DEV_GUILD_ID:
            guild = discord.Object(id=int(DEV_GUILD_ID))
            self.tree.copy_global_to(guild=guild)
            await self.tree.sync(guild=guild)
            log.info("Synced slash commands to dev guild %s", DEV_GUILD_ID)
        else:
            await self.tree.sync()
            log.info("Synced slash commands globally (can take up to an hour to appear).")


bot = SilenceBot()


@bot.event
async def on_ready():
    log.info("Logged in as %s (id: %s)", bot.user, bot.user.id if bot.user else "?")


# --------------------------------------------------------------------------
# /silence
# --------------------------------------------------------------------------


@bot.tree.command(name="silence", description="Deny @everyone the Speak permission in your current voice channel.")
@app_commands.default_permissions(**{REQUIRED_PERMISSION: True})
@app_commands.checks.has_permissions(**{REQUIRED_PERMISSION: True})
@app_commands.guild_only()
async def silence(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)

    member = interaction.user
    guild = interaction.guild
    assert guild is not None  # guaranteed by guild_only()

    voice_state = member.voice
    if voice_state is None or voice_state.channel is None:
        await interaction.followup.send(
            "You need to be connected to a voice channel to use this command."
        )
        return

    channel = voice_state.channel
    if not isinstance(channel, discord.VoiceChannel):
        await interaction.followup.send(
            "This only works in standard voice channels, not stage channels."
        )
        return

    if guild.me is None or not channel.permissions_for(guild.me).manage_roles:
        await interaction.followup.send(
            "I don't have the **Manage Roles** permission in that channel, "
            "so I can't change its permissions. See README.md for the invite link."
        )
        return

    everyone = guild.default_role

    already_silenced = await bot.store.get(channel.id)
    if already_silenced is not None:
        # Don't clobber the originally-saved state with a second capture --
        # just make sure Speak is still denied and let the user know.
        overwrite = channel.overwrites_for(everyone)
        if overwrite.speak is not False:
            overwrite.speak = False
            try:
                await channel.set_permissions(
                    everyone, overwrite=overwrite, reason=f"Re-applied by /silence ({member})"
                )
            except discord.Forbidden:
                await interaction.followup.send(
                    "I don't have permission to manage permissions in that channel."
                )
                return
        await interaction.followup.send(f"\U0001F507 {channel.mention} is already silenced.")
        return

    had_overwrite = everyone in channel.overwrites
    overwrite = channel.overwrites_for(everyone)
    previous_speak = overwrite.speak  # True, False, or None -- saved as-is

    overwrite.speak = False
    try:
        await channel.set_permissions(
            everyone, overwrite=overwrite, reason=f"Silenced by {member} via /silence"
        )
    except discord.Forbidden:
        await interaction.followup.send(
            "I don't have permission to manage permissions in that channel. "
            "I need the **Manage Roles** permission."
        )
        return

    await bot.store.set(channel.id, previous_speak, had_overwrite)

    log.info(
        "Silenced #%s (%s) in guild %s -- requested by %s. previous_speak=%r had_overwrite=%r",
        channel.name, channel.id, guild.name, member, previous_speak, had_overwrite,
    )

    await interaction.followup.send(
        f"\U0001F507 Silenced **{channel.name}** -- Only Mclovin and Generals can speak. "
        f"No one was server-muted, and existing per-role/per-member overrides "
        f"(including any explicit Speak allow) are untouched."
    )


# --------------------------------------------------------------------------
# /unsilence
# --------------------------------------------------------------------------


@bot.tree.command(
    name="unsilence",
    description="Restore @everyone's Speak permission in a voice channel to how it was before /silence.",
)
@app_commands.describe(channel="Voice channel to unsilence (defaults to the one you're connected to).")
@app_commands.default_permissions(**{REQUIRED_PERMISSION: True})
@app_commands.checks.has_permissions(**{REQUIRED_PERMISSION: True})
@app_commands.guild_only()
async def unsilence(interaction: discord.Interaction, channel: Optional[discord.VoiceChannel] = None):
    await interaction.response.defer(ephemeral=True)

    member = interaction.user
    guild = interaction.guild
    assert guild is not None  # guaranteed by guild_only()

    target_channel = channel
    if target_channel is None:
        voice_state = member.voice
        if voice_state is not None and isinstance(voice_state.channel, discord.VoiceChannel):
            target_channel = voice_state.channel

    if target_channel is None:
        await interaction.followup.send(
            "Specify a voice channel, or join one, then try again."
        )
        return

    if guild.me is None or not target_channel.permissions_for(guild.me).manage_roles:
        await interaction.followup.send(
            "I don't have the **Manage Roles** permission in that channel, "
            "so I can't change its permissions."
        )
        return

    everyone = guild.default_role
    record = await bot.store.get(target_channel.id)

    if record is None:
        await interaction.followup.send(
            f"No silence record found for {target_channel.mention}. It may not have "
            f"been silenced with `/silence`, or has already been restored."
        )
        return

    overwrite = target_channel.overwrites_for(everyone)
    overwrite.speak = record["previous_speak"]

    try:
        if overwrite.is_empty() and not record["had_overwrite"]:
            # No @everyone overwrite existed before /silence, and nothing's
            # left to set now -- remove the entry instead of leaving a
            # no-op overwrite behind.
            await target_channel.set_permissions(
                everyone, overwrite=None, reason=f"Unsilenced by {member} via /unsilence"
            )
        else:
            await target_channel.set_permissions(
                everyone, overwrite=overwrite, reason=f"Unsilenced by {member} via /unsilence"
            )
    except discord.Forbidden:
        await interaction.followup.send(
            "I don't have permission to manage permissions in that channel. "
            "I need the **Manage Roles** permission."
        )
        return

    await bot.store.clear(target_channel.id)

    log.info(
        "Unsilenced #%s (%s) in guild %s -- requested by %s. restored_speak=%r",
        target_channel.name, target_channel.id, guild.name, member, record["previous_speak"],
    )

    await interaction.followup.send(
        f"\U0001F50A Restored **{target_channel.name}**'s Speak permission to its previous state."
    )


# --------------------------------------------------------------------------
# /unverified
# --------------------------------------------------------------------------


@bot.tree.command(name="unverified", description="List the members who currently have the Unverified role.")
@app_commands.default_permissions(manage_channels=True)
@app_commands.checks.has_permissions(manage_channels=True)
@app_commands.guild_only()
async def unverified(interaction: discord.Interaction):
    guild = interaction.guild
    assert guild is not None  # guaranteed by guild_only()

    role = guild.get_role(UNVERIFIED_ROLE_ID)
    if role is None:
        await interaction.response.send_message(
            f"I couldn't find the Unverified role (ID {UNVERIFIED_ROLE_ID}) in this server.",
            ephemeral=True,
        )
        return

    # Deliberately NOT ephemeral: the result is posted in the channel where
    # the command was used.
    await interaction.response.defer()

    # Make sure the member cache is complete so the list can't come back short.
    if not guild.chunked:
        await guild.chunk()

    # Read-only: this only looks at who currently holds the role.
    members = sorted(role.members, key=lambda m: m.display_name.lower())

    if not members:
        await interaction.followup.send("\u2705 There are currently no unverified members.")
        return

    max_listed = 50  # Far above the usual ~10; keeps the message under Discord's 2,000-character limit.
    lines = [f"- {m.display_name}" for m in members[:max_listed]]
    if len(members) > max_listed:
        lines.append(f"...and {len(members) - max_listed} more.")

    log.info(
        "Listed %d unverified member(s) in guild %s -- requested by %s.",
        len(members), guild.name, interaction.user,
    )

    # Plain-text display names, deliberately NOT mentions: clickable mentions were
    # showing as "unknown-user" for members the reader's app hadn't cached, while
    # plain text always displays correctly. allowed_mentions stays at none as a
    # safeguard, so a display name that contains "@everyone" can never ping.
    await interaction.followup.send(
        f"**Unverified members: {len(members)}**\n" + "\n".join(lines),
        allowed_mentions=discord.AllowedMentions.none(),
    )


# --------------------------------------------------------------------------
# /limited
#
# Works like /unverified, but lists the members who have the Limited Access role
# (voice channels only). It posts a list of names for everyone in the channel to
# see, so it only works in the Officers channels (OFFICER_CHANNEL_IDS, near the top
# of this file). Anywhere else it gives the person a private (ephemeral) refusal
# and shows nothing. Like /unverified, it needs Manage Channels.
# --------------------------------------------------------------------------

# Said in the refusal outside the Officers channels, and shown in italics under the heading of the list.
_LIMITED_OFFICERS_ONLY = "This command can only be used in Officers channels."


@bot.tree.command(
    name="limited",
    description="List the members who currently have the Limited Access role (Officers channels only).",
)
@app_commands.default_permissions(manage_channels=True)
@app_commands.checks.has_permissions(manage_channels=True)
@app_commands.guild_only()
async def limited(interaction: discord.Interaction):
    guild = interaction.guild
    assert guild is not None  # guaranteed by guild_only()

    # The Officers-channels-only rule. It comes first, before anything about the members is looked up,
    # so in any other channel nothing is read or shown. The refusal is ephemeral: only the person who
    # used the command sees it.
    if interaction.channel_id not in OFFICER_CHANNEL_IDS:
        await interaction.response.send_message(_LIMITED_OFFICERS_ONLY, ephemeral=True)
        return

    limited_role = guild.get_role(LIMITED_ACCESS_ROLE_ID)
    if limited_role is None:
        await interaction.response.send_message(
            f"I couldn't find the Limited Access role (ID {LIMITED_ACCESS_ROLE_ID}) in this server.",
            ephemeral=True,
        )
        return

    # Deliberately NOT ephemeral, same as /unverified: the result is posted in the Officers channel
    # where the command was used.
    await interaction.response.defer()

    # Same step as /unverified: make sure the member cache is complete so the list can't come back short.
    if not guild.chunked:
        await guild.chunk()

    # Read-only: this only looks at who currently holds the role. Sorted exactly like /unverified.
    members = sorted(limited_role.members, key=lambda m: m.display_name.lower())

    if not members:
        await interaction.followup.send("✅ There are currently no Limited Access members.")
        return

    max_listed = 50  # Same cap as /unverified. Fifty 32-character names plus the two heading lines still
    # fit under Discord's 2,000-character limit.
    lines = [f"- {m.display_name}" for m in members[:max_listed]]
    if len(members) > max_listed:
        lines.append(f"...and {len(members) - max_listed} more.")

    log.info(
        "Listed %d Limited Access member(s) in guild %s -- requested by %s.",
        len(members), guild.name, interaction.user,
    )

    # Plain-text display names, exactly as in /unverified: not mentions, and allowed_mentions stays at
    # none so a display name containing "@everyone" can never ping.
    await interaction.followup.send(
        f"**Limited Access members (voice channels only): {len(members)}**\n"
        f"*{_LIMITED_OFFICERS_ONLY}*\n" + "\n".join(lines),
        allowed_mentions=discord.AllowedMentions.none(),
    )


# --------------------------------------------------------------------------
# /commands
# --------------------------------------------------------------------------
@bot.tree.command(name="commands", description="Show this bot's commands and what they do.")
async def commands_help(interaction: discord.Interaction):
    await interaction.response.send_message(
        "**Available commands**\n"
        "`/silence` -- Stops everyone from speaking in the voice channel you're in "
        "(Generals are not affected; nobody is server-muted).\n"
        "`/unsilence` -- Restores everyone's Speak permission to exactly how it was "
        "before /silence.\n"
        "`/mute` -- Server-mutes a member who is in voice for a set time (1 minute to 24 hours); "
        "they are unmuted automatically.\n"
        "`/unmute` -- Ends a timed mute started with /mute early.\n"
        "`/unverified` -- Lists everyone who currently has the Unverified role, with a count.\n"
        "`/limited` -- Lists everyone who currently has the Limited Access role, with a count (Officers channels only).\n"
        "`/tkl` -- Verify a new member to the Discord.\n"
        "`/rem` -- A utility command for Poss.\n"
        "`/ban` -- Bans a user, even if they have left (pick from the suggestions or enter their user ID).\n"
        "`/kick` -- Kicks a member (pick from the suggestions or enter their user ID).\n"
        "`/unverify` -- Takes away all of a member's roles and gives them the Unverified role (pick from the suggestions or enter their user ID; asks you first).\n"
        "`/define` -- Looks up a word or phrase in the Merriam-Webster dictionary and shows its definitions.\n"
        "`/urban` -- Posts an Urban Dictionary definition for a word or phrase (if it's available).\n"
        "`/sos` -- Calls for help in Cyrodiil PvP and pings the SOS role. Shared 30-minute cooldown "
        "for the whole server -- no exceptions.\n"
        "`/roster` -- A short guide to using the roster and signing up for a group. Anyone can use it.\n"
        + _esom_commands_line(interaction) +
        "`/commands` -- Shows this list.",
        ephemeral=True,
        allowed_mentions=discord.AllowedMentions.none(),
    )


# --------------------------------------------------------------------------
# /mute
# --------------------------------------------------------------------------


@bot.tree.command(name="mute", description="Server-mute a member who is in voice for a set time.")
@app_commands.describe(
    member="The member to mute (they must be in a voice channel).",
    duration="How long the mute lasts.",
    reason="Optional reason, shown to the member and in the moderation log.",
)
@app_commands.choices(duration=[app_commands.Choice(name=label, value=seconds) for label, seconds in MUTE_DURATIONS])
@app_commands.default_permissions(mute_members=True)
@app_commands.checks.has_permissions(mute_members=True)
@app_commands.guild_only()
async def mute(
    interaction: discord.Interaction,
    # Typed as User (not Member) so that someone who has just left gets a friendly
    # reply from us instead of a generic error; we look up the real Member ourselves.
    member: discord.User,
    duration: app_commands.Choice[int],
    reason: Optional[app_commands.Range[str, 1, 300]] = None,
):
    # Private ("Only you can see this"): nothing is posted in the channel.
    await interaction.response.defer(ephemeral=True)

    guild = interaction.guild
    assert guild is not None  # guaranteed by guild_only()
    none = discord.AllowedMentions.none()

    if duration.value not in {seconds for _, seconds in MUTE_DURATIONS}:
        await interaction.followup.send("That isn’t one of the available durations.", ephemeral=True, allowed_mentions=none)
        return

    result = await bot.mutes.start_mute(guild, member, interaction.user, duration.value, reason)
    if result.error:
        await interaction.followup.send(result.error, ephemeral=True, allowed_mentions=none)
        return

    record = result.record
    expires = _parse_time(record["expires_at"])
    lines = [
        f"\U0001F507 Muted **{discord.utils.escape_markdown(record['member_name'])}** for **{duration.name}**.",
        f"Ends: {_fmt_end(expires)}",
    ]
    if reason:
        lines.append(f"Reason: {reason}")
    lines.append(f"Case: `{record['id']}`")
    if not result.dm_sent:
        lines.append(
            "⚠️ The mute is active, but I couldn't DM them "
            "(their DMs may be closed, or they may have blocked me)."
        )
    if not result.logged:
        lines.append(
            "⚠️ The mute is active, but I couldn't post it to the moderation-log channel. "
            "Please tell an admin; the details are in the bot's logs."
        )
    if not result.saved:
        lines.append(
            "⚠️ The mute is active, but I couldn't save its final record to disk. The copy saved "
            "just before muting should still let me finish it after a restart; please tell an admin."
        )
    await interaction.followup.send("\n".join(lines), ephemeral=True, allowed_mentions=none)


# --------------------------------------------------------------------------
# /unmute
# --------------------------------------------------------------------------


@bot.tree.command(name="unmute", description="End a timed mute started with /mute early.")
@app_commands.describe(member="The member whose timed mute should end.")
@app_commands.default_permissions(mute_members=True)
@app_commands.checks.has_permissions(mute_members=True)
@app_commands.guild_only()
async def unmute(interaction: discord.Interaction, member: discord.User):
    await interaction.response.defer(ephemeral=True)

    guild = interaction.guild
    assert guild is not None  # guaranteed by guild_only()

    message = await bot.mutes.stop_mute(guild, member.id, interaction.user)
    await interaction.followup.send(message, ephemeral=True, allowed_mentions=discord.AllowedMentions.none())


# --------------------------------------------------------------------------
# /tkl
#
# Replaces the old Carl-bot verification tag. It first asks the moderator, in a
# private ephemeral message, to choose Full Access (The Kings Legion role) or
# Limited Access (voice channels only) -- see _TklAccessView. Only once that's
# answered does it swap the Unverified role for whichever role was chosen,
# announce the approval in the channel (with a real ping for the member), and
# write a separate audit entry noting which access level was given.
#
# Who may use it is decided ONLY by TKL_STAFF_ROLE_IDS, checked inside the
# command. There is deliberately no @default_permissions or @has_permissions
# decorator here: those would lock out staff who happen to lack some unrelated
# Discord permission.
# --------------------------------------------------------------------------

_tkl_busy: Set[str] = set()  # members being verified right now ("guild:member"), so two staff can't clash

# What the bot needs in a channel to post an embed there: (permission name, label shown to people).
_POST_PERMISSIONS = (
    ("view_channel", "View Channel"),
    ("send_messages", "Send Messages"),
    ("embed_links", "Embed Links"),
)


async def _tkl_reply(interaction: discord.Interaction, text: str) -> None:
    """Every error and the final result go to the moderator only ("Only you can see this")."""
    await interaction.followup.send(text, ephemeral=True, allowed_mentions=discord.AllowedMentions.none())


def _is_tkl_staff(user: Any) -> bool:
    return any(role.id in TKL_STAFF_ROLE_IDS for role in getattr(user, "roles", ()))


def _has_role(member: discord.Member, role_id: int) -> bool:
    return any(role.id == role_id for role in member.roles)


def _cannot_post_in(channel: Any, me: Optional[discord.Member]) -> str:
    """Why the bot can't post an embed in this channel, or "" if it can."""
    if channel is None or isinstance(channel, discord.PartialMessageable):
        return "I can't see that channel"
    if me is None or not hasattr(channel, "permissions_for"):
        return "I couldn't check my permissions there"
    permissions = channel.permissions_for(me)
    missing = [label for flag, label in _POST_PERMISSIONS if not getattr(permissions, flag)]
    return ("I'm missing permissions there: " + ", ".join(missing)) if missing else ""


def _tkl_audit_channel(guild: discord.Guild) -> Tuple[Optional[discord.TextChannel], str]:
    """The mod-log channel if it can be used right now, otherwise (None, why not)."""
    channel = guild.get_channel(MOD_LOG_CHANNEL_ID)
    if channel is None:
        if bot.get_channel(MOD_LOG_CHANNEL_ID) is not None:
            return None, "it belongs to a different server"
        return None, "I can't find it, or I can't see it"
    if not isinstance(channel, discord.TextChannel):
        return None, "it isn't a text channel"
    problem = _cannot_post_in(channel, guild.me)
    return (None, problem) if problem else (channel, "")


def _tkl_failed_cleanly(exc: BaseException) -> bool:
    """True if Discord definitely refused the request, so nothing changed. False for a timeout or a
    server error, where the change may or may not have gone through."""
    return isinstance(exc, discord.HTTPException) and exc.status < 500


def _tkl_member_gone(exc: BaseException) -> bool:
    """True if the error means the member is no longer in the server (not, say, a deleted role)."""
    return isinstance(exc, discord.NotFound) and getattr(exc, "code", 0) in (10007, 10013)


def _tkl_why(exc: BaseException) -> str:
    """A short, private explanation of a failed role change (no technical details)."""
    if isinstance(exc, discord.Forbidden):
        return "Discord wouldn’t let me change their roles (is my role above the Unverified role and the role you picked?)"
    if isinstance(exc, discord.HTTPException):
        return f"Discord returned an error ({exc.status})"
    return "an unexpected error happened (details are in the bot's logs)"


async def _tkl_restore(
    member: discord.Member, unverified: discord.Role, grant_role: discord.Role, *,
    remove_granted: bool, readd_unverified: bool, reason: str,
) -> Optional[List[str]]:
    """Put back whatever a failed /tkl may have changed.

    Returns the roles that could NOT be restored, or None if the member has left the server (so there is
    nothing left to restore).
    """
    failed: List[str] = []
    if readd_unverified:
        try:
            await member.add_roles(unverified, reason=reason)
        except Exception as exc:
            if _tkl_member_gone(exc):
                log.warning("/tkl roll-back: %s (%s) has left the server, so there is nothing to restore", member, member.id)
                return None
            log.exception("/tkl roll-back failed: could not put the %s role back on %s (%s)", unverified.name, member, member.id)
            # Stop here. Taking the granted role away as well could leave them with NEITHER role,
            # which nobody would notice; leaving it on is the safer mistake.
            return [unverified.name]
    if remove_granted:
        try:
            await member.remove_roles(grant_role, reason=reason)
        except Exception as exc:
            if _tkl_member_gone(exc):
                log.warning("/tkl roll-back: %s (%s) has left the server, so there is nothing to restore", member, member.id)
                return None
            log.exception("/tkl roll-back failed: could not take the %s role off %s (%s)", grant_role.name, member, member.id)
            failed.append(grant_role.name)
    return failed


async def _tkl_swap_roles(
    member: discord.Member, unverified: discord.Role, grant_role: discord.Role, had_role: bool,
    moderator: discord.Member, note: Optional[str],
) -> Optional[str]:
    """Give grant_role (The Kings Legion role for Full Access, or the Limited Access role), then take
    the Unverified role away.

    Returns None when both worked. Otherwise it returns the private message for the moderator, and the
    roles have been put back as they were whenever that was possible.

    The order is deliberate. Even if the second step fails and the roll-back fails too, the member keeps
    at least one of the two roles, most likely both: they still show up in /unverified and /tkl can
    simply be run again. The other way round could leave them with NEITHER role, which nobody would notice.
    """
    name = discord.utils.escape_markdown(member.display_name)
    reason = f"Verified by {moderator.display_name} ({moderator.id}) via /tkl"
    if note:
        reason += f": {note}"
    reason = reason[:512]  # Discord's limit for audit-log reasons
    undo_reason = f"Rolling back a failed /tkl by {moderator.display_name} ({moderator.id})"
    gone = f"**{name}** is no longer in the server, so nothing was changed."

    added = False
    if not had_role:
        try:
            await member.add_roles(grant_role, reason=reason)
            added = True
        except Exception as exc:
            if _tkl_member_gone(exc):
                log.warning("/tkl: %s (%s) left the server before they could be verified", member, member.id)
                return gone
            log.exception("/tkl: could not give the %s role to %s (%s)", grant_role.name, member, member.id)
            if _tkl_failed_cleanly(exc):
                return f"I couldn’t verify **{name}**: {_tkl_why(exc)}. Their roles are unchanged and nothing was sent."
            # A timeout or server error: the role may have been added anyway, so make sure it is gone.
            failed = await _tkl_restore(
                member, unverified, grant_role, remove_granted=True, readd_unverified=False, reason=undo_reason
            )
            if failed is None:
                return gone
            if failed:
                return (
                    f"⚠️ I couldn’t verify **{name}**: {_tkl_why(exc)}. I also couldn’t confirm that the "
                    f"{discord.utils.escape_markdown(grant_role.name)} role wasn’t added, so please check their roles "
                    "in Discord. Nothing was sent."
                )
            return f"I couldn’t verify **{name}**: {_tkl_why(exc)}. Their roles are unchanged and nothing was sent."

    try:
        await member.remove_roles(unverified, reason=reason)
    except Exception as exc:
        if _tkl_member_gone(exc):
            log.warning("/tkl: %s (%s) left the server before they could be verified", member, member.id)
            return gone
        log.exception("/tkl: could not take the %s role off %s (%s)", unverified.name, member, member.id)
        failed = await _tkl_restore(
            member, unverified, grant_role,
            remove_granted=added, readd_unverified=not _tkl_failed_cleanly(exc), reason=undo_reason,
        )
        if failed is None:
            return gone
        if failed:
            return (
                f"⚠️ I couldn’t finish verifying **{name}**: {_tkl_why(exc)}. I also couldn’t undo my changes "
                f"({', '.join(discord.utils.escape_markdown(role) for role in failed)}), so their roles may be wrong now. "
                "Please check them in Discord: they should have exactly one of the Unverified and "
                f"{discord.utils.escape_markdown(grant_role.name)} roles. Nothing was sent."
            )
        return (
            f"I couldn’t verify **{name}**: {_tkl_why(exc)}. I put their roles back exactly as they were, "
            "and nothing was sent."
        )
    return None


def _tkl_approval_embed(member: discord.Member, note: Optional[str]) -> discord.Embed:
    # The member is pinged by the message CONTENT (see _tkl_verify); the mention in here is only text.
    embed = discord.Embed(
        title="Application approved",
        description=(
            f"{member.mention}, welcome to The Kings Legion Discord! head over to "
            f"<#{ROLE_SELECTION_CHANNEL_ID}> and choose all the roles that apply to you."
        ),
        colour=discord.Colour(0x2ECC71),
    )
    if note:
        embed.add_field(name="Note from moderator:", value=note, inline=False)
    return embed


def _tkl_audit_embed(
    member: discord.Member, moderator: discord.Member, unverified: discord.Role, grant_role: discord.Role,
    access_label: str, had_role: bool, note: Optional[str],
) -> discord.Embed:
    # Plain text only (names, never mentions): this embed must not ping or link anyone.
    embed = discord.Embed(
        title="Member verified",
        description=(
            f"**{discord.utils.escape_markdown(member.display_name)}** was verified by "
            f"**{discord.utils.escape_markdown(moderator.display_name)}**."
        ),
        colour=discord.Colour(0x2ECC71),
    )
    embed.add_field(name="Member", value=_who(member.display_name, member.id), inline=True)
    embed.add_field(name="Verified by", value=_who(moderator.display_name, moderator.id), inline=True)
    embed.add_field(name="Access level", value=access_label, inline=True)
    unverified_name, grant_name = discord.utils.escape_markdown(unverified.name), discord.utils.escape_markdown(grant_role.name)
    embed.add_field(
        name="Roles",
        value=f"Removed: {unverified_name}\n" + (f"Already had: {grant_name}" if had_role else f"Added: {grant_name}"),
        inline=False,
    )
    if note:
        embed.add_field(name="Note from moderator:", value=note, inline=False)
    embed.timestamp = _utcnow()
    return embed


_TKL_ACCESS_TIMEOUT = 120  # seconds the Full Access / Limited Access buttons stay usable


def _tkl_access_embed(member: discord.Member, moderator: Any) -> discord.Embed:
    """The private, ephemeral choice shown before /tkl changes any roles."""
    name = discord.utils.escape_markdown(member.display_name)
    return discord.Embed(
        title="Choose an access level",
        description=(
            f"Verifying **{name}**. Pick which role to give them -- nothing is changed until you do.\n\n"
            "🟢 **Full Access** -- removes Unverified, gives The Kings Legion role (full server access).\n"
            "🔴 **Limited Access** -- removes Unverified, gives the Limited Access role (voice channels only).\n\n"
            f"Only {discord.utils.escape_markdown(moderator.display_name)} can answer this, and it expires "
            f"after {_TKL_ACCESS_TIMEOUT} seconds if nobody picks."
        ),
        colour=discord.Colour(0x3498DB),
    )


async def _tkl_finish(
    interaction: discord.Interaction, guild: discord.Guild, moderator: discord.Member, member: discord.Member,
    unverified: discord.Role, grant_role: discord.Role, access_label: str, note: Optional[str],
    channel: Any, audit_channel: discord.TextChannel,
) -> None:
    """Runs once a Full Access / Limited Access button has been pressed: gives grant_role, takes the
    Unverified role away, tells the channel and the mod-log, then updates the access-choice message
    with the private result. Otherwise does exactly what /tkl used to do immediately, just
    parametrised by whichever role was picked.

    Answers the button press straight away (Discord only waits 3 seconds for that) with a short
    placeholder, the same way /rem's Yes button answers immediately before its own longer-running
    work -- the role changes and two message sends below can occasionally take longer than that.
    """
    name = discord.utils.escape_markdown(member.display_name)
    message = interaction.message  # the access-choice message; editable long after the 3-second window
    await interaction.response.edit_message(content=f"Verifying **{name}**…", embed=None, view=None)

    async def finish(text: str) -> None:
        if message is not None:
            try:
                await message.edit(content=text)
                return
            except Exception:
                log.warning("/tkl: could not update the access-choice message with the result", exc_info=True)
        # The message is gone, or couldn't be edited: a fresh ephemeral reply still gets the result
        # to the moderator.
        await _tkl_reply(interaction, text)

    had_role = _has_role(member, grant_role.id)
    failure = await _tkl_swap_roles(member, unverified, grant_role, had_role, moderator, note)
    if failure is not None:
        await finish(failure)  # nothing is announced when verification failed
        return
    log.info(
        "/tkl: %s (%s) verified by %s (%s) in guild %s with %s",
        member, member.id, moderator, moderator.id, guild.name, access_label,
    )

    # --- Tell people. A failure here never undoes the roles; it is reported to the moderator. -----
    # Mentions inside the note are defused (and the embed can't ping anyway); the only ping allowed
    # on the public message is the verified member.
    shown_note = discord.utils.escape_mentions(note) if note else None
    warnings: List[str] = []

    approval = None
    try:
        approval = await channel.send(
            content=member.mention,
            embed=_tkl_approval_embed(member, shown_note),
            allowed_mentions=discord.AllowedMentions(everyone=False, users=[member], roles=False, replied_user=False),
        )
    except Exception:
        log.exception("/tkl: could not post the approval message for %s (%s)", member, member.id)
        warnings.append(
            "⚠️ The roles were changed, but I couldn’t post the approval message in this channel, "
            "so the member hasn’t been told or pinged. Please let them know yourself."
        )
    if approval is not None:
        try:
            await approval.add_reaction("✅")  # the check mark the old Carl-bot tag added
        except Exception:
            log.warning("/tkl: could not add the check-mark reaction to the approval message", exc_info=True)

    try:
        await audit_channel.send(
            embed=_tkl_audit_embed(member, moderator, unverified, grant_role, access_label, had_role, shown_note),
            allowed_mentions=discord.AllowedMentions.none(),
        )
    except Exception:
        log.exception("/tkl: could not post the audit entry for %s (%s)", member, member.id)
        warnings.append(
            "⚠️ The roles were changed, but I couldn’t post the audit entry. "
            "Please tell an admin; the details are in the bot's logs."
        )

    unverified_name = discord.utils.escape_markdown(unverified.name)
    grant_name = discord.utils.escape_markdown(grant_role.name)
    if had_role:
        done = f"✅ Verified **{name}** with **{access_label}**: removed {unverified_name}. They already had {grant_name}."
    else:
        done = f"✅ Verified **{name}** with **{access_label}**: removed {unverified_name} and added {grant_name}."
    await finish("\n".join([done] + warnings))


class _TklAccessView(discord.ui.View):
    """The Full Access / Limited Access buttons shown before /tkl changes any roles. This message is
    ephemeral, so only the moderator who ran /tkl ever sees it at all; nothing changes until one of
    the two buttons is pressed."""

    def __init__(
        self, guild: discord.Guild, moderator: discord.Member, target: discord.Member,
        unverified: discord.Role, kings: discord.Role, limited: discord.Role,
        note: Optional[str], channel: Any, audit_channel: discord.TextChannel, key: str,
    ) -> None:
        super().__init__(timeout=_TKL_ACCESS_TIMEOUT)
        self.guild = guild
        self.moderator = moderator
        self.target = target
        self.unverified = unverified
        self.kings = kings
        self.limited = limited
        self.note = note
        self.channel = channel
        self.audit_channel = audit_channel
        self.key = key
        self.message: Optional[discord.Message] = None  # the choice itself; set once it has been sent
        self._answered = False  # set by the first press of either button, so nothing can be processed twice
        self._released = False  # set once _tkl_busy has been freed, so that only ever happens once

    def _release(self) -> None:
        """Let another /tkl on this member start. Safe to call more than once."""
        if not self._released:
            self._released = True
            _tkl_busy.discard(self.key)

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.moderator.id:
            await interaction.response.send_message(
                "Only the moderator who ran /tkl for this member can use these buttons.", ephemeral=True,
            )
            return False
        if not _is_tkl_staff(interaction.user):
            await interaction.response.send_message(
                "You no longer have a staff role, so you can’t answer this.", ephemeral=True,
            )
            return False
        return True

    async def _first_answer(self, interaction: discord.Interaction) -> bool:
        """True for the first press only. Any later press (a double click, or one button right
        after the other) is ignored."""
        if self._answered:
            await interaction.response.defer()
            return False
        self._answered = True  # no await between the check and this line, so two presses can't both get through
        self.stop()
        return True

    async def _choose(self, interaction: discord.Interaction, grant_role: discord.Role, label: str) -> None:
        try:
            await _tkl_finish(
                interaction, self.guild, self.moderator, self.target, self.unverified, grant_role, label,
                self.note, self.channel, self.audit_channel,
            )
        finally:
            self._release()

    @discord.ui.button(label="Full Access", style=discord.ButtonStyle.success)
    async def full_access(self, interaction: discord.Interaction, button: discord.ui.Button) -> None:
        if not await self._first_answer(interaction):
            return
        await self._choose(interaction, self.kings, "Full Access")

    @discord.ui.button(label="Limited Access", style=discord.ButtonStyle.danger)
    async def limited_access(self, interaction: discord.Interaction, button: discord.ui.Button) -> None:
        if not await self._first_answer(interaction):
            return
        await self._choose(interaction, self.limited, "Limited Access")

    async def on_timeout(self) -> None:
        if self._answered:
            return
        self._answered = True
        self._release()
        if self.message is not None:
            try:
                await self.message.edit(
                    content=(
                        "Nobody picked an access level in time, so nothing was changed. "
                        "Run /tkl again if you still want to verify them."
                    ),
                    embed=None, view=None,
                )
            except Exception:
                log.warning("/tkl: could not update the access-choice message after it timed out", exc_info=True)

    async def on_error(self, interaction: discord.Interaction, error: Exception, item: discord.ui.Item) -> None:
        log.error("Unhandled error in the /tkl access buttons", exc_info=error)
        self._release()
        text = "Something went wrong with that button. Please check their roles in Discord before trying again."
        try:
            if interaction.response.is_done():
                await interaction.followup.send(text, ephemeral=True)
            else:
                await interaction.response.send_message(text, ephemeral=True)
        except Exception:
            log.warning("/tkl: could not tell the moderator that a button failed", exc_info=True)


async def _tkl_verify(
    interaction: discord.Interaction, guild: discord.Guild, moderator: discord.Member,
    target: discord.User, note: Optional[str], key: str,
) -> None:
    """Checks everything /tkl needs up front, then shows the Full Access / Limited Access choice.
    Nothing is changed here -- see _tkl_finish, run from inside _TklAccessView once a button is
    pressed."""

    async def reply(text: str) -> None:
        await _tkl_reply(interaction, text)

    handed_off = False  # set True once _TklAccessView takes over responsibility for _tkl_busy
    try:
        # --- Look at the member as Discord sees them right now (not a possibly stale copy). -----------
        try:
            member = await guild.fetch_member(target.id)
        except discord.NotFound:
            await reply("That user isn’t a member of this server.")
            return
        except discord.HTTPException:
            log.warning("/tkl: could not fetch %s (%s) from Discord; using the cached member", target, target.id)
            member = guild.get_member(target.id) or (target if isinstance(target, discord.Member) else None)
            if member is None:
                await reply("I couldn’t look that member up just now (Discord didn’t answer). Please try again in a moment.")
                return
        name = discord.utils.escape_markdown(member.display_name)

        # --- All three roles must exist in this server. ------------------------------------------------
        unverified = guild.get_role(UNVERIFIED_ROLE_ID)
        if unverified is None:
            await reply(f"I couldn’t find the Unverified role (ID {UNVERIFIED_ROLE_ID}) in this server, so I haven’t changed anything.")
            return
        kings = guild.get_role(KINGS_LEGION_ROLE_ID)
        if kings is None:
            await reply(f"I couldn’t find The Kings Legion role (ID {KINGS_LEGION_ROLE_ID}) in this server, so I haven’t changed anything.")
            return
        limited = guild.get_role(LIMITED_ACCESS_ROLE_ID)
        if limited is None:
            await reply(f"I couldn’t find the Limited Access role (ID {LIMITED_ACCESS_ROLE_ID}) in this server, so I haven’t changed anything.")
            return

        # --- The member must actually be unverified. ---------------------------------------------------
        if not _has_role(member, UNVERIFIED_ROLE_ID):
            await reply(
                f"**{name}** isn’t currently unverified (they don’t have the Unverified role), "
                "so I haven’t changed any roles or sent anything."
            )
            return

        # --- Can the bot actually make either change? --------------------------------------------------
        me = guild.me
        if me is None or not me.guild_permissions.manage_roles:
            await reply("I don’t have the **Manage Roles** permission, so I can’t change anyone’s roles. I haven’t changed anything.")
            return
        for role in (unverified, kings, limited):
            role_name = discord.utils.escape_markdown(role.name)
            if role.managed:
                await reply(
                    f"The **{role_name}** role is managed by an integration, so it can’t be given or taken away "
                    "manually. I haven’t changed anything."
                )
                return
            if not me.top_role > role:
                await reply(
                    f"My highest role isn’t above the **{role_name}** role, so Discord won’t let me give or remove it. "
                    "Please move my role above it (Server Settings → Roles). I haven’t changed anything."
                )
                return
        if member.id == guild.owner_id or not me.top_role > member.top_role:
            await reply(
                f"I can’t change **{name}**’s roles because their highest role is at or above mine "
                "(or they own the server). I haven’t changed anything."
            )
            return

        # --- Both places the bot will post in must be usable BEFORE any role is touched. --------------
        audit_channel, problem = _tkl_audit_channel(guild)
        if audit_channel is None:
            await reply(
                f"I can’t use the mod-log channel ({problem}), so I haven’t changed any roles. "
                "Please ask an admin to check it."
            )
            return
        channel = interaction.channel
        problem = _cannot_post_in(channel, me)
        if problem:
            await reply(
                f"I can’t post in this channel ({problem}), so I haven’t changed any roles. "
                "Try again in a channel where I can send messages and embeds."
            )
            return

        # --- Ask which access level, instead of changing anything yet. ---------------------------------
        view = _TklAccessView(guild, moderator, member, unverified, kings, limited, note, channel, audit_channel, key)
        view.message = await interaction.followup.send(
            embed=_tkl_access_embed(member, moderator), view=view, ephemeral=True,
            allowed_mentions=discord.AllowedMentions.none(),
        )
        handed_off = True  # _TklAccessView now owns releasing _tkl_busy, whichever way this goes
    finally:
        if not handed_off:
            _tkl_busy.discard(key)


@bot.tree.command(name="tkl", description="Verify a member to the Discord.")
@app_commands.describe(
    member="The member to verify.",
    note="Optional note from you, shown in the approval message and in the audit log.",
)
@app_commands.guild_only()
async def tkl(
    interaction: discord.Interaction,
    # Typed as User (not Member) so that someone who has just left gets a friendly
    # reply from us instead of a generic error; we look up the real Member ourselves.
    member: discord.User,
    note: Optional[app_commands.Range[str, 1, 500]] = None,
):
    # Private ("Only you can see this"): errors and the final result go only to the moderator.
    await interaction.response.defer(ephemeral=True)

    guild = interaction.guild
    assert guild is not None  # guaranteed by guild_only()
    moderator = interaction.user

    async def reply(text: str) -> None:
        await _tkl_reply(interaction, text)

    # The staff-role allowlist is the whole authorisation check.
    if not _is_tkl_staff(moderator):
        log.info("/tkl refused: %s (%s) has none of the staff roles", moderator, moderator.id)
        await reply("You don't have permission to use this command.")
        return
    if member.id == moderator.id:
        await reply("You can’t verify yourself. Ask another staff member to run /tkl for you.")
        return
    if member.bot:
        await reply("That’s a bot account, so it can’t be verified.")
        return

    note = note.strip() if note else None
    if not note:
        note = None  # a blank note counts as no note, so no empty field is ever shown

    key = _key(guild.id, member.id)
    if key in _tkl_busy:
        await reply("Someone is already verifying that member. Please wait a moment and try again.")
        return
    _tkl_busy.add(key)
    # _tkl_verify releases _tkl_busy itself on every path (an early validation failure, or once
    # _TklAccessView takes over and later releases it when a button is pressed, errors, or times out).
    await _tkl_verify(interaction, guild, moderator, member, note, key)


# --------------------------------------------------------------------------
# /rem
#
# Replaces the old Carl-bot "?rem" tag: it takes the Role Confirmed role away
# from everyone who has it. Because that changes a lot of people at once, it
# first asks "Are you sure?" with a green Yes and a red No button that only the
# moderator who ran the command can press. Nothing is changed until Yes is
# pressed.
#
# Only the Role Confirmed role is ever removed: no other role is touched and
# nobody is kicked or banned.
# --------------------------------------------------------------------------

# The role /rem takes away from everyone. It's looked up by ID, not name, so
# renaming the role in Discord won't break the command.
ROLE_CONFIRMED_ROLE_ID = 1387563821362577620

_REM_CONFIRM_TIMEOUT = 60       # seconds the Yes / No buttons stay usable
_REM_RETRY_DELAYS = (2, 5, 15)  # seconds to wait before trying one member again after a temporary Discord error
_REM_STOP_AFTER = 10            # stop after this many failures in a row: something is wrong for everyone, not one member
_REM_UPDATE_EVERY = 15          # seconds between progress updates on the message
_REM_LIST_MAX = 10              # how many members who couldn't be changed are named in the summary

_rem_busy: Set[int] = set()  # servers where a /rem removal is running right now, so two can't overlap


def _rem_problem(guild: discord.Guild) -> Tuple[Optional[discord.Role], str]:
    """The Role Confirmed role if the bot can remove it right now, otherwise (None, why not)."""
    role = guild.get_role(ROLE_CONFIRMED_ROLE_ID)
    if role is None:
        return None, f"I couldn’t find the Role Confirmed role (ID {ROLE_CONFIRMED_ROLE_ID}) in this server, so I haven’t changed anything."
    role_name = discord.utils.escape_markdown(role.name)
    me = guild.me
    if me is None or not me.guild_permissions.manage_roles:
        return None, "I don’t have the **Manage Roles** permission, so I can’t remove anyone’s roles. I haven’t changed anything."
    if role.managed:
        return None, f"The **{role_name}** role is managed by an integration, so it can’t be taken away manually. I haven’t changed anything."
    if not me.top_role > role:
        return None, (
            f"My highest role isn’t above the **{role_name}** role, so Discord won’t let me remove it. "
            "Please move my role above it (Server Settings → Roles). I haven’t changed anything."
        )
    return role, ""


class _RemOutcome:
    """What a /rem removal did, so the summary can say exactly that and nothing more."""

    def __init__(self, total: int) -> None:
        self.total = total  # members who had the role when the removal started
        self.removed = 0  # Discord confirmed the role is gone
        self.skipped = 0  # left the server, or no longer had the role by the time I got to them
        self.failed: List[Tuple[str, int, str]] = []  # (name, user ID, why) for members I couldn't change
        self.stopped = ""  # why it stopped early, or "" if it ran to the end
        self.seconds = 0.0

    @property
    def not_attempted(self) -> int:
        # Worked out from the other numbers, so the counts can never add up to more or less than the total.
        return self.total - self.removed - self.skipped - len(self.failed)


def _rem_why(exc: BaseException) -> str:
    """A short explanation of a failed removal (no technical details)."""
    if isinstance(exc, discord.Forbidden):
        return "Discord wouldn’t let me change their roles (their highest role is probably at or above mine)"
    if isinstance(exc, discord.HTTPException):
        return f"Discord returned an error ({exc.status})"
    return "an unexpected error happened (details are in the bot’s logs)"


def _rem_temporary(exc: BaseException) -> bool:
    """True for errors worth trying again in a moment: Discord is busy or didn't answer."""
    if isinstance(exc, discord.HTTPException):
        return exc.status == 429 or exc.status >= 500
    return isinstance(exc, (asyncio.TimeoutError, OSError))


async def _rem_one(member: discord.Member, role: discord.Role, reason: str) -> Optional[BaseException]:
    """Take the role off one member. Returns None if Discord confirmed it, otherwise the error that stopped it.

    discord.py already waits out Discord's rate limits by itself; this also tries again a few times when
    Discord reports a temporary problem.
    """
    for attempt in range(len(_REM_RETRY_DELAYS) + 1):
        try:
            # atomic=True (discord.py's default, written out because it matters here) asks Discord to remove just this
            # one role from this one member. atomic=False would instead send back the member's WHOLE role list as the
            # bot has it cached, which can wipe out a role somebody else gave them a moment ago (or bring back one
            # that was just taken away). /rem runs for a long time, so that is a real risk.
            await member.remove_roles(role, reason=reason, atomic=True)
            return None
        except Exception as exc:
            if not _rem_temporary(exc) or attempt == len(_REM_RETRY_DELAYS):
                return exc
            log.warning(
                "/rem: temporary problem taking the role off %s (%s): %r; trying again in %s seconds",
                member, member.id, exc, _REM_RETRY_DELAYS[attempt],
            )
            await asyncio.sleep(_REM_RETRY_DELAYS[attempt])
    return None  # not reached: the last attempt always returns above


async def _rem_remove_all(
    guild: discord.Guild, role: discord.Role, members: List[discord.Member], moderator: Any, progress: Any = None,
) -> _RemOutcome:
    """Take the role off every member in the list, one at a time, and keep an honest count of what happened.

    A member only counts as removed when Discord confirmed it. `progress`, if given, is an async function that
    is called now and then with the outcome so far (it must not raise). This never raises: an unexpected
    problem just ends the run early and is reported in the outcome.
    """
    outcome = _RemOutcome(len(members))
    loop = asyncio.get_running_loop()
    started = last_update = loop.time()
    reason = f"Removed by {moderator.display_name} ({moderator.id}) via /rem"[:512]  # 512: Discord's audit-log limit
    try:
        me = guild.me
        if me is None:
            outcome.stopped = "I couldn’t check my own roles"
            return outcome

        # Unlike /ban, /kick, and /tkl's verification step, a plain role removal isn't checked against the
        # MEMBER's highest role at all -- only the role being removed has to sit below the bot's own top role,
        # which _rem_problem() already confirmed once, up front, before this function was even called. So nobody
        # (owner included) is pre-filtered out here for holding some other, higher role: every member who has
        # the role is attempted, and Discord's own response to that attempt (handled below) is the only word on
        # whether any single one goes through.
        todo: List[discord.Member] = list(members)

        in_a_row = 0  # failures since the last success
        for member in todo:
            # Look at the member as the bot knows them right now: they may have left or lost the role already.
            current = guild.get_member(member.id)
            if current is None or current.get_role(role.id) is None:
                outcome.skipped += 1
            else:
                error = await _rem_one(current, role, reason)
                if error is None:
                    outcome.removed += 1
                    in_a_row = 0
                elif _tkl_member_gone(error):
                    outcome.skipped += 1  # they left while I was working
                else:
                    log.warning("/rem: could not take the role off %s (%s): %r", current, current.id, error)
                    outcome.failed.append((current.display_name, current.id, _rem_why(error)))
                    in_a_row += 1
                    if in_a_row >= _REM_STOP_AFTER:
                        outcome.stopped = f"{_REM_STOP_AFTER} removals in a row failed, so I stopped instead of trying everyone else"
                        break
            if progress is not None and loop.time() - last_update >= _REM_UPDATE_EVERY:
                last_update = loop.time()
                await progress(outcome)
    except Exception:
        log.exception("/rem stopped unexpectedly")
        outcome.stopped = "an unexpected error happened (details are in the bot’s logs)"
    finally:
        outcome.seconds = loop.time() - started
    return outcome


def _rem_embed(title: str, description: str, colour: int) -> discord.Embed:
    return discord.Embed(title=title, description=description, colour=discord.Colour(colour))


def _rem_elapsed(seconds: float) -> str:
    minutes, rest = divmod(int(seconds), 60)
    return f"{minutes}m {rest}s" if minutes else f"{rest}s"


def _rem_confirm_embed(role: discord.Role, moderator: Any, count: int) -> discord.Embed:
    who = "**1** member who currently has it" if count == 1 else f"**{count}** members who currently have it"
    return _rem_embed(
        "Are you sure?",
        f"Do you want to remove the **{discord.utils.escape_markdown(role.name)}** role from {who}?\n"
        "No other roles are changed, and nobody is kicked or banned.\n\n"
        f"Only {discord.utils.escape_markdown(moderator.display_name)} can answer this. Nothing is changed "
        f"unless **Yes** is pressed, and the question expires after {_REM_CONFIRM_TIMEOUT} seconds.",
        0xE67E22,
    )


def _rem_working_embed(role: discord.Role, moderator: Any, so_far: Optional[_RemOutcome]) -> discord.Embed:
    text = (
        f"Started by **{discord.utils.escape_markdown(moderator.display_name)}**. If there are a lot of members "
        "this can take a while, because Discord limits how fast roles can be changed."
    )
    if so_far is not None:
        handled = so_far.removed + so_far.skipped + len(so_far.failed)
        text += f"\n\nProgress: **{handled}** of **{so_far.total}** members handled so far."
    return _rem_embed(f"Removing the {role.name} role…", text, 0xE67E22)


def _rem_summary_embed(role: discord.Role, moderator: Any, outcome: _RemOutcome) -> discord.Embed:
    name = discord.utils.escape_markdown(role.name)
    if outcome.total == 0:
        return _rem_embed("Nothing to remove", f"Nobody has the **{name}** role any more, so nothing was changed.", 0x95A5A6)

    lines = [f"Removed the **{name}** role from **{outcome.removed}** of **{outcome.total}** members."]
    if outcome.skipped:
        lines.append(f"{outcome.skipped} had already left the server or lost the role by the time I got to them.")
    if outcome.failed:
        lines.append(f"**{len(outcome.failed)}** couldn’t be changed and still have the role.")
    if outcome.not_attempted:
        lines.append(
            f"**{outcome.not_attempted}** were not tried, because I stopped early "
            f"({outcome.stopped or 'something went wrong'}). Run /rem again to carry on: "
            "it only affects members who still have the role."
        )
    if outcome.failed:
        shown = outcome.failed[:_REM_LIST_MAX]
        lines.append("\n**Couldn’t change:**")
        lines.extend(f"- {_who(failed_name, failed_id)}: {why}" for failed_name, failed_id, why in shown)
        if len(outcome.failed) > len(shown):
            lines.append(f"…and {len(outcome.failed) - len(shown)} more (see the bot’s logs).")

    if outcome.failed or outcome.not_attempted:
        title = "Role removal stopped early" if outcome.not_attempted else "Role removal finished with problems"
        colour = 0xE74C3C if outcome.removed == 0 else 0xE67E22
    else:
        title, colour = "Role removal complete", 0x2ECC71
    embed = _rem_embed(title, "\n".join(lines)[:4000], colour)
    embed.set_footer(text=f"Started by {moderator.display_name} · took {_rem_elapsed(outcome.seconds)}")
    return embed


async def _rem_edit(message: Optional[discord.Message], embed: discord.Embed) -> bool:
    """Show a new embed on the /rem message and take its buttons away. False if that didn't work (e.g. it was deleted)."""
    if message is None:
        return False
    try:
        await message.edit(embed=embed, view=None)
        return True
    except Exception:
        log.warning("/rem: could not update the message", exc_info=True)
        return False


async def _rem_finish(interaction: discord.Interaction, message: Optional[discord.Message], embed: discord.Embed) -> None:
    """Show the final result: on the message if it can still be edited, otherwise as a new message in the channel."""
    if await _rem_edit(message, embed):
        return
    channel = interaction.channel
    if channel is None:
        log.error("/rem: there is no channel to post the result in")
        return
    try:
        await channel.send(embed=embed, allowed_mentions=discord.AllowedMentions.none())
    except Exception:
        log.exception("/rem: could not show the result anywhere in Discord")


async def _rem_run(interaction: discord.Interaction, guild: discord.Guild, role: discord.Role) -> None:
    """After Yes: remove the role from everyone who has it, keep the message up to date, and say exactly what happened."""
    moderator = interaction.user
    # interaction.message is a normal message. Unlike the slash command's own reply it can still be edited more
    # than 15 minutes later, which matters because a big removal can take that long.
    message = interaction.message
    # Answer the button press straight away (Discord only waits 3 seconds) and swap the buttons for a progress message.
    await interaction.response.edit_message(embed=_rem_working_embed(role, moderator, None), view=None)

    try:
        if not guild.chunked:
            await guild.chunk()
    except Exception:
        log.exception("/rem: could not load the member list")
        await _rem_finish(interaction, message, _rem_embed(
            "Nothing was changed",
            "I couldn’t get the list of members from Discord, so I haven’t removed anything. Please try again in a moment.",
            0xE74C3C,
        ))
        return
    members = list(role.members)

    can_edit = True

    async def progress(so_far: _RemOutcome) -> None:
        nonlocal can_edit
        if can_edit:
            can_edit = await _rem_edit(message, _rem_working_embed(role, moderator, so_far))

    outcome = await _rem_remove_all(guild, role, members, moderator, progress)
    log.info(
        "/rem: run by %s (%s) in guild %s: %d member(s) had the role; removed %d, skipped %d, failed %d, not tried %d%s.",
        moderator, moderator.id, guild.name, outcome.total, outcome.removed, outcome.skipped, len(outcome.failed),
        outcome.not_attempted, f" (stopped early: {outcome.stopped})" if outcome.stopped else "",
    )
    await _rem_finish(interaction, message, _rem_summary_embed(role, moderator, outcome))


class _RemConfirmView(discord.ui.View):
    """The Yes / No buttons under the /rem question. Only the moderator who ran /rem can press them."""

    def __init__(self, moderator: Any) -> None:
        super().__init__(timeout=_REM_CONFIRM_TIMEOUT)
        self.moderator = moderator
        self.message: Optional[discord.Message] = None  # the question itself; set once it has been sent
        self._answered = False  # set by the first press of either button, so nothing can be processed twice

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.moderator.id:
            await interaction.response.send_message(
                "Only the moderator who ran /rem can use these buttons.", ephemeral=True,
            )
            return False
        if not interaction.permissions.manage_guild:
            await interaction.response.send_message(
                "You no longer have the **Manage Server** permission, so you can’t answer this.", ephemeral=True,
            )
            return False
        return True

    async def _first_answer(self, interaction: discord.Interaction) -> bool:
        """True for the first press only. Any later press (a double click, or No right after Yes) is ignored."""
        if self._answered:
            await interaction.response.defer()
            return False
        self._answered = True  # no await between the check and this line, so two presses can't both get through
        self.stop()
        return True

    @discord.ui.button(label="Yes", style=discord.ButtonStyle.success)
    async def yes(self, interaction: discord.Interaction, button: discord.ui.Button) -> None:
        if not await self._first_answer(interaction):
            return
        guild = interaction.guild
        assert guild is not None  # guaranteed by guild_only()

        # Look everything up again: some time has passed since the question was asked.
        role, problem = _rem_problem(guild)
        if role is None:
            await interaction.response.edit_message(embed=_rem_embed("Nothing was changed", problem, 0xE74C3C), view=None)
            return
        if guild.id in _rem_busy:
            await interaction.response.edit_message(
                embed=_rem_embed("Nothing was changed", "Another /rem removal is already running in this server.", 0xE74C3C),
                view=None,
            )
            return
        _rem_busy.add(guild.id)
        try:
            await _rem_run(interaction, guild, role)
        finally:
            _rem_busy.discard(guild.id)

    @discord.ui.button(label="No", style=discord.ButtonStyle.danger)
    async def no(self, interaction: discord.Interaction, button: discord.ui.Button) -> None:
        if not await self._first_answer(interaction):
            return
        await interaction.response.edit_message(
            embed=_rem_embed("Cancelled", "No roles were changed.", 0x95A5A6), view=None,
        )

    async def on_timeout(self) -> None:
        if self._answered:
            return
        self._answered = True
        await _rem_edit(self.message, _rem_embed(
            "Timed out",
            "Nobody answered in time, so no roles were changed. Run /rem again if you still want to do this.",
            0x95A5A6,
        ))

    async def on_error(self, interaction: discord.Interaction, error: Exception, item: discord.ui.Item) -> None:
        log.error("Unhandled error in the /rem buttons", exc_info=error)
        text = "Something went wrong with that button."
        try:
            if interaction.response.is_done():
                await interaction.followup.send(text, ephemeral=True)
            else:
                await interaction.response.send_message(text, ephemeral=True)
        except Exception:
            log.warning("/rem: could not tell the user that a button failed", exc_info=True)


@bot.tree.command(name="rem", description="Removes the Role Confirmed role from everyone.")
@app_commands.default_permissions(manage_guild=True)
@app_commands.checks.has_permissions(manage_guild=True)
@app_commands.guild_only()
async def rem(interaction: discord.Interaction):
    guild = interaction.guild
    assert guild is not None  # guaranteed by guild_only()
    none = discord.AllowedMentions.none()

    # Problems found now are shown only to the moderator ("Only you can see this").
    role, problem = _rem_problem(guild)
    if role is None:
        await interaction.response.send_message(problem, ephemeral=True, allowed_mentions=none)
        return
    if guild.id in _rem_busy:
        await interaction.response.send_message(
            "A /rem removal is already running in this server. Please wait for it to finish.",
            ephemeral=True, allowed_mentions=none,
        )
        return

    # Make sure the member list is complete before anyone is counted (the same step /unverified takes).
    deferred = not guild.chunked
    if deferred:
        await interaction.response.defer()
        await guild.chunk()
    count = len(role.members)
    if count == 0:
        text = f"Nobody currently has the **{discord.utils.escape_markdown(role.name)}** role, so there is nothing to remove."
        if deferred:
            await interaction.followup.send(text, allowed_mentions=none)
        else:
            await interaction.response.send_message(text, ephemeral=True, allowed_mentions=none)
        return

    # Ask first. Nothing is removed until Yes is pressed (see _RemConfirmView).
    view = _RemConfirmView(interaction.user)
    embed = _rem_confirm_embed(role, interaction.user, count)
    if deferred:
        view.message = await interaction.followup.send(embed=embed, view=view, allowed_mentions=none)
    else:
        await interaction.response.send_message(embed=embed, view=view, allowed_mentions=none)
        view.message = await interaction.original_response()


# --------------------------------------------------------------------------
# /con
#
# A small convenience command for Poss only: paste a message link and it
# replies privately with a ready-to-copy "Jump to Roster" heading that links
# to it. Deliberately left out of /commands. It doesn't change anything in
# the server -- it only reads the link that's typed in.
# --------------------------------------------------------------------------

_CON_LINK_RE = re.compile(
    r"^https://(?:canary\.|ptb\.)?discord(?:app)?\.com/channels/\d{17,20}/\d{17,20}/\d{17,20}(?:[/?#].*)?$"
)


@bot.tree.command(name="con", description="Simple utility command for Poss.")
@app_commands.describe(link="A message link (long-press or right-click a message → Copy Message Link).")
@app_commands.default_permissions(manage_guild=True)
@app_commands.checks.has_permissions(manage_guild=True)
@app_commands.guild_only()
async def con(interaction: discord.Interaction, link: app_commands.Range[str, 1, 200]):
    link = link.strip()
    if not _CON_LINK_RE.match(link):
        await interaction.response.send_message(
            "That doesn’t look like a message link. Long-press (or right-click) the message and choose "
            "**Copy Message Link**, then paste it here.",
            ephemeral=True,
        )
        return
    # Plain content, not an embed: Discord's mobile "Copy Text" only copies a message's own content,
    # not an embed's, and being able to copy this is the whole point of the command.
    # The copyable box has TWO backticks on each side, not one, because the second line has backticks of its
    # own (around /roster). With only one backtick on each side, the box would end at the first of those.
    await interaction.response.send_message(
        f"``### [Jump to Roster]({link})\n-# Use `/roster` for tutorial on how to sign up``",
        ephemeral=True, allowed_mentions=discord.AllowedMentions.none(),
    )


# --------------------------------------------------------------------------
# /ban and /kick
#
# Both take the person as a text box with suggestions, not as Discord's User
# picker. The picker can only list people Discord knows to be in the server, so
# it can't take the ID of someone who has left. Here, typing a name shows
# matching members to pick from, and typing or pasting any Discord user ID works
# too. Each action is announced in the channel it was used in and written to the
# mod-log channel (MOD_LOG_CHANNEL_ID), like /mute and /tkl.
#
# /ban asks first: it shows the moderator a private question with three buttons
# (Ban + Delete 24h, Ban Only, Cancel) and bans nobody until a ban button is pressed.
# --------------------------------------------------------------------------

_mod_busy: Set[str] = set()  # "guild:user" pairs being banned or kicked right now, so two moderators can't clash
_BAN_CONFIRM_TIMEOUT = 60  # seconds the /ban buttons stay usable


def _parse_user_id(text: str) -> Optional[int]:
    """The Discord user ID in what was typed: the bare number, or a pasted mention like <@123...>. None if it isn't one."""
    text = text.strip()
    if text.startswith("<@") and text.endswith(">"):
        text = text[2:-1]
        if text.startswith("!"):
            text = text[1:]
    if not (text.isascii() and text.isdigit() and 17 <= len(text) <= 19):
        return None
    value = int(text)
    return value if value < 2 ** 63 else None


def _member_choice(member: discord.Member) -> app_commands.Choice[str]:
    # The ID is always shown in full, so two people with the same name can be told apart.
    tail = f" (@{member.name}) · {member.id}"
    return app_commands.Choice(name=member.display_name[: 100 - len(tail)] + tail, value=str(member.id))


def _user_choices(interaction: discord.Interaction, current: str, permission: str) -> List[app_commands.Choice[str]]:
    """The suggestions under the user box of /ban and /kick: members whose name contains what has been typed so far.

    Only people who may use the command are shown any. A user ID that has been typed is offered as the first
    choice, so it can be picked as well as simply submitted. Discord allows at most 25 choices.
    """
    guild = interaction.guild
    if guild is None or not getattr(interaction.permissions, permission, False):
        return []
    text = current.strip()
    choices: List[app_commands.Choice[str]] = []

    typed_id = _parse_user_id(text)
    if typed_id is not None:
        typed_member = guild.get_member(typed_id)
        if typed_member is not None:
            choices.append(_member_choice(typed_member))
        else:
            choices.append(app_commands.Choice(name=f"Use the user ID {typed_id}", value=str(typed_id)))

    needle = text.lower()
    if needle:
        starts: List[discord.Member] = []  # names that begin with the text come first
        contains: List[discord.Member] = []
        for member in guild.members:
            names = (member.display_name.lower(), member.name.lower(), (member.global_name or "").lower())
            if any(name.startswith(needle) for name in names):
                starts.append(member)
                if len(starts) >= 25:
                    break
            elif any(needle in name for name in names):
                contains.append(member)
        taken = {choice.value for choice in choices}
        for member in starts + contains:
            if len(choices) >= 25:
                break
            if str(member.id) not in taken:
                choices.append(_member_choice(member))
    return choices[:25]


def _mod_audit_embed(
    is_kick: bool, name: str, target_id: int, was_member: bool, moderator: Any, reason: Optional[str],
    delete_seconds: Optional[int] = None,
) -> discord.Embed:
    # Plain text only (names, never mentions): this embed must not ping or link anyone.
    done = "kicked" if is_kick else "banned"
    description = (
        f"**{discord.utils.escape_markdown(name)}** was {done} by "
        f"**{discord.utils.escape_markdown(moderator.display_name)}**."
    )
    if not was_member:
        description += " They were not in the server."
    embed = discord.Embed(
        title="Member kicked" if is_kick else "Member banned" if was_member else "User banned",
        description=description,
        colour=discord.Colour(0xE67E22 if is_kick else 0xE74C3C),
    )
    embed.add_field(name="Action", value="Kick" if is_kick else "Ban", inline=True)
    embed.add_field(name="Member" if was_member else "User", value=_who(name, target_id), inline=True)
    embed.add_field(name="Moderator", value=_who(moderator.display_name, moderator.id), inline=True)
    embed.add_field(
        name="Reason", value=discord.utils.escape_mentions(reason) if reason else "No reason provided", inline=False,
    )
    if delete_seconds is not None:  # a ban: also record what the moderator chose, and whether they were still in the server
        embed.add_field(name="In the server", value="Yes" if was_member else "No", inline=True)
        embed.add_field(name="Message deletion", value="Previous 24 hours" if delete_seconds else "None", inline=True)
    embed.timestamp = _utcnow()
    return embed


async def _mod_log(guild: discord.Guild, embed: discord.Embed) -> str:
    """Post one entry to the mod-log channel. Never raises. Returns "" if it was posted, otherwise a short reason why not."""
    try:
        channel, problem = await bot.mutes._log_channel(guild.id)  # the same channel and checks /mute uses
        if channel is None:
            log.error("Mod-log channel unavailable (%s); could not post an entry", problem)
            return problem
        await asyncio.wait_for(
            channel.send(embed=embed, allowed_mentions=discord.AllowedMentions.none()),
            timeout=_SEND_TIMEOUT,
        )
        return ""
    except Exception:
        log.exception("Could not post an entry to the mod-log channel")
        return "Discord refused it or didn’t answer"


def _mod_failure_text(is_kick: bool, name: str, exc: BaseException) -> str:
    """The private message for a /ban or /kick that Discord didn't carry out (no technical details)."""
    verb, done = ("kick", "kicked") if is_kick else ("ban", "banned")
    if isinstance(exc, discord.Forbidden):
        return (
            f"Discord wouldn’t let me {verb} **{name}**. Please check that I have the "
            f"**{'Kick' if is_kick else 'Ban'} Members** permission and that my role is above theirs. Nothing was changed."
        )
    if isinstance(exc, discord.NotFound):
        if is_kick:
            return f"**{name}** is no longer in the server, so nothing was changed."
        return "Discord says that user doesn’t exist, so nothing was changed."
    if _tkl_failed_cleanly(exc):
        return f"I couldn’t {verb} **{name}**: Discord returned an error ({getattr(exc, 'status', '?')}). Nothing was changed."
    # A timeout or server error: it may or may not have gone through, so nothing is announced or logged.
    return (
        f"I couldn’t confirm whether **{name}** was {done}, because Discord didn’t answer properly. Please check "
        f"{'the member list' if is_kick else 'the ban list'} in Server Settings before trying again. "
        "I haven’t announced or logged anything."
    )


def _ban_confirm_embed(name: str, target_id: int, was_member: bool, reason: Optional[str]) -> discord.Embed:
    """The private question /ban asks: who would be banned, why, and what each button does."""
    embed = _rem_embed(
        "Ban this user?",
        f"Do you want to ban **{discord.utils.escape_markdown(discord.utils.escape_mentions(name))}**?\n\n"
        "**Ban + Delete 24h** bans them and deletes their messages from the previous 24 hours.\n"
        "**Ban Only** bans them and leaves their messages alone.\n"
        "**Cancel** does nothing.",
        0xE74C3C,
    )
    embed.add_field(name="User", value=_who(name, target_id), inline=True)
    embed.add_field(name="In the server", value="Yes" if was_member else "No", inline=True)
    embed.add_field(
        name="Reason", value=discord.utils.escape_mentions(reason) if reason else "No reason provided", inline=False,
    )
    embed.set_footer(
        text=f"Only you can see this. Nothing happens until you press a ban button, and this expires after {_BAN_CONFIRM_TIMEOUT} seconds.",
    )
    return embed


async def _mod_reply(interaction: discord.Interaction, text: str, after_buttons: bool) -> None:
    """Every error and the final result of /ban and /kick go to the moderator only ("Only you can see this").

    Normally that is a private follow-up, the same as /tkl. After a ban button was pressed the text instead replaces
    the question in the same private message. By then the ban may already have happened, so that path never raises.
    """
    if not after_buttons:
        await _tkl_reply(interaction, text)
        return
    none = discord.AllowedMentions.none()
    try:
        await interaction.edit_original_response(content=text, embed=None, view=None, allowed_mentions=none)
    except Exception:
        log.warning("/ban: could not replace the question with the result; sending it as a new private message", exc_info=True)
        try:
            await interaction.followup.send(text, ephemeral=True, allowed_mentions=none)
        except Exception:
            log.exception("/ban: could not show the moderator the result")


class _BanConfirmView(discord.ui.View):
    """The buttons under the /ban question. Only the moderator who ran /ban can press them."""

    def __init__(self, interaction: discord.Interaction, target_id: int, reason: Optional[str], safe_name: str) -> None:
        super().__init__(timeout=_BAN_CONFIRM_TIMEOUT)
        self.ban_command = interaction  # the /ban command itself: its private reply IS the question, so it is edited if time runs out
        self.moderator = interaction.user
        self.target_id, self.reason, self.safe_name = target_id, reason, safe_name
        self._answered = False  # set by the first press of any button, so nothing can be processed twice

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.moderator.id:
            await interaction.response.send_message("Only the moderator who ran /ban can use these buttons.", ephemeral=True)
            return False
        if not interaction.permissions.ban_members:
            await interaction.response.send_message(
                "You no longer have the **Ban Members** permission, so you can’t answer this.", ephemeral=True,
            )
            return False
        return True

    async def _answer(self, interaction: discord.Interaction, embed: discord.Embed) -> bool:
        """For the first press only: answer it straight away (Discord only waits 3 seconds) by taking the buttons away
        and showing `embed`. Returns False for any later press (a double tap, or another button straight after).

        The view is deliberately not stopped. Until it times out by itself, a repeated tap is still acknowledged quietly;
        a stopped view would drop it and Discord would show "This interaction failed".
        """
        if self._answered:
            await interaction.response.defer()
            return False
        self._answered = True  # no await between the check and this line, so two presses can't both get through
        try:
            await interaction.response.edit_message(embed=embed, view=None)
        except Exception:
            self._answered = False  # Discord didn't take the press, so nothing has started: they can press again
            raise
        return True

    async def _ban(self, interaction: discord.Interaction, delete_seconds: int) -> None:
        working = _rem_embed("Banning…", f"Banning **{self.safe_name}**. This only takes a moment.", 0xE74C3C)
        if await self._answer(interaction, working):
            # Everything is looked up and checked again, because some time has passed since the question was asked.
            # The result then replaces the "Banning…" message.
            await _mod_action(interaction, False, str(self.target_id), self.reason, delete_seconds)

    @discord.ui.button(label="Ban + Delete 24h", style=discord.ButtonStyle.danger)
    async def ban_and_delete(self, interaction: discord.Interaction, button: discord.ui.Button) -> None:
        await self._ban(interaction, 86400)  # 86400 seconds: Discord deletes their messages from the previous 24 hours

    @discord.ui.button(label="Ban Only", style=discord.ButtonStyle.danger)
    async def ban_only(self, interaction: discord.Interaction, button: discord.ui.Button) -> None:
        await self._ban(interaction, 0)  # 0 seconds: none of their messages are deleted

    @discord.ui.button(label="Cancel", style=discord.ButtonStyle.secondary)
    async def cancel(self, interaction: discord.Interaction, button: discord.ui.Button) -> None:
        await self._answer(interaction, _rem_embed("Cancelled", "Nobody was banned and no messages were deleted.", 0x95A5A6))

    async def on_timeout(self) -> None:
        if self._answered:
            return
        self._answered = True
        try:
            await self.ban_command.edit_original_response(embed=_rem_embed(
                "Timed out",
                "Nobody answered in time, so nobody was banned and no messages were deleted. "
                "Run /ban again if you still want to do this.",
                0x95A5A6,
            ), view=None)
        except Exception:
            log.warning("/ban: could not update the expired question", exc_info=True)

    async def on_error(self, interaction: discord.Interaction, error: Exception, item: discord.ui.Item) -> None:
        log.error("Unhandled error in the /ban buttons", exc_info=error)
        text = (
            "Something went wrong with that button, so I can’t be sure what happened. "
            "Please check the ban list in Server Settings before trying again."
        )
        try:
            if interaction.response.is_done():
                await interaction.edit_original_response(content=text, embed=None, view=None)
            else:
                await interaction.response.send_message(text, ephemeral=True)
        except Exception:
            log.warning("/ban: could not tell the user that a button failed", exc_info=True)


async def _mod_do(
    interaction: discord.Interaction, is_kick: bool, target_id: int, reason: Optional[str], me: discord.Member,
    delete_seconds: Optional[int] = None,
) -> None:
    """Look the person up, check everything, do the ban or kick, then announce and log it.

    /ban stops after the checks to ask the moderator first (see _BanConfirmView): delete_seconds is None until a ban
    button has been pressed, and then it is how many seconds of the person's messages Discord should delete.
    """
    guild = interaction.guild
    assert guild is not None  # guaranteed by guild_only()
    moderator = interaction.user
    verb, done = ("kick", "kicked") if is_kick else ("ban", "banned")
    none = discord.AllowedMentions.none()

    async def reply(text: str) -> None:
        await _mod_reply(interaction, text, delete_seconds is not None)  # private to the moderator

    # --- Who is it? Ask Discord now (not a possibly stale copy). ---------------------------------------
    member: Optional[discord.Member] = None
    checked = True  # False if Discord couldn't say whether they are in the server
    try:
        member = await guild.fetch_member(target_id)
    except discord.NotFound:
        pass  # not in the server
    except discord.HTTPException:
        log.warning("/%s: could not fetch %s from Discord; using the cached member", verb, target_id)
        member = guild.get_member(target_id)
        checked = member is not None

    target: Any = member
    if is_kick:
        if member is None:
            if checked:
                await reply("That user isn’t a member of this server, so they can’t be kicked.")
            else:
                await reply("I couldn’t look that member up just now (Discord didn’t answer). Please try again in a moment.")
            return
    elif member is None:
        # A ban doesn't need them to be in the server, only to be a real Discord account.
        try:
            target = await bot.fetch_user(target_id)
        except discord.NotFound:
            await reply("I couldn’t find a Discord user with that ID. Please check it and try again.")
            return
        except discord.HTTPException:
            await reply("I couldn’t look that user up just now (Discord didn’t answer). Please try again in a moment.")
            return

    # The best name there is, captured NOW (before the action): the server nickname for a member, otherwise
    # their global display name or username. It is plain text because they may not be in the server afterwards.
    name = (target.display_name or "").strip() or f"User {target_id}"
    safe = discord.utils.escape_markdown(discord.utils.escape_mentions(name))

    # --- Is it allowed? ----------------------------------------------------------------------------
    if member is not None:
        if member.id == guild.owner_id:
            await reply(f"I can’t {verb} **{safe}** because they own the server. I haven’t changed anything.")
            return
        if moderator.id != guild.owner_id and not moderator.top_role > member.top_role:
            await reply(f"You can’t {verb} **{safe}** because their highest role is at or above yours. I haven’t changed anything.")
            return
        if not me.top_role > member.top_role:
            await reply(
                f"I can’t {verb} **{safe}** because their highest role is at or above mine. "
                "Please move my role above theirs (Server Settings → Roles). I haven’t changed anything."
            )
            return
    if not is_kick:
        try:
            await guild.fetch_ban(discord.Object(id=target_id))
        except discord.NotFound:
            pass  # not banned yet: carry on
        except discord.HTTPException:
            log.warning("/ban: could not check whether %s is already banned; going ahead", target_id)
        else:
            await reply(f"**{safe}** is already banned, so I haven’t changed anything.")
            return

    if not is_kick and delete_seconds is None:
        # Ask first, privately. Nothing is banned or deleted until a ban button is pressed (see _BanConfirmView).
        view = _BanConfirmView(interaction, target_id, reason, safe)
        await interaction.edit_original_response(
            embed=_ban_confirm_embed(name, target_id, member is not None, reason), view=view, allowed_mentions=none,
        )
        return

    # --- The action itself. The reason goes to Discord's audit log as well as the mod-log channel. ---
    audit_reason = f"{done.capitalize()} by {moderator.display_name} ({moderator.id}) via /{verb}: {reason or 'No reason provided'}"[:512]
    try:
        if is_kick:
            await guild.kick(member, reason=audit_reason)
        else:
            # delete_message_seconds is always given, because discord.py's default (when it is left out) is to delete
            # 24 hours of the person's messages. Here it is exactly what the moderator chose: 86400 or 0.
            await guild.ban(discord.Object(id=target_id), reason=audit_reason, delete_message_seconds=delete_seconds)
    except Exception as exc:
        log.exception("/%s: could not %s %s (%s)", verb, verb, name, target_id)
        await reply(_mod_failure_text(is_kick, safe, exc))
        return
    log.info("/%s: %s (%s) %s by %s (%s) in guild %s", verb, name, target_id, done, moderator, moderator.id, guild.name)

    # --- Tell people. A failure here never undoes the action; it is reported to the moderator. ---------
    warnings: List[str] = []
    channel = interaction.channel
    posted = False
    if channel is not None:
        try:
            await channel.send(f"**{safe}** {done}.", allowed_mentions=none)
            posted = True
        except Exception:
            log.exception("/%s: could not post the public message for %s (%s)", verb, name, target_id)
    if not posted:
        warnings.append(f"⚠️ The {verb} went through, but I couldn’t post the message in this channel.")

    problem = await _mod_log(
        guild, _mod_audit_embed(is_kick, name, target_id, member is not None, moderator, reason, delete_seconds),
    )
    if problem:
        warnings.append(
            f"⚠️ The {verb} went through, but I couldn’t post it to the mod-log channel ({problem}). "
            "Please tell an admin; the details are in the bot’s logs."
        )

    result = f"✅ {done.capitalize()} **{safe}** (`{target_id}`)."
    if member is None:
        result += " They were not in the server."
    if not is_kick:
        result += (
            " I asked Discord to delete their messages from the previous 24 hours." if delete_seconds
            else " I didn’t delete any of their messages."
        )
    await reply("\n".join([result] + warnings))


async def _mod_action(
    interaction: discord.Interaction, is_kick: bool, user: str, reason: Optional[str], delete_seconds: Optional[int] = None,
) -> None:
    """The checks /ban and /kick share before anyone is looked up. The interaction has already been acknowledged.

    It runs twice for a ban: when /ban is used (delete_seconds is None, so _mod_do only asks) and again when a ban
    button is pressed (delete_seconds is 86400 or 0, so _mod_do goes ahead).
    """
    guild = interaction.guild
    assert guild is not None  # guaranteed by guild_only()
    moderator = interaction.user
    verb = "kick" if is_kick else "ban"

    async def reply(text: str) -> None:
        await _mod_reply(interaction, text, delete_seconds is not None)

    target_id = _parse_user_id(user)
    if target_id is None:
        await reply(
            "That doesn’t look like a Discord user ID. Pick someone from the suggestions as you type, "
            "or enter their user ID (17 to 19 digits)."
        )
        return
    if target_id == moderator.id:
        await reply(f"You can’t {verb} yourself.")
        return
    if bot.user is not None and target_id == bot.user.id:
        await reply(f"I can’t {verb} myself.")
        return

    me = guild.me
    if me is None or not (me.guild_permissions.kick_members if is_kick else me.guild_permissions.ban_members):
        await reply(
            f"I don’t have the **{'Kick' if is_kick else 'Ban'} Members** permission, so I can’t {verb} anyone. "
            "I haven’t changed anything."
        )
        return

    key = _key(guild.id, target_id)
    if key in _mod_busy:
        await reply("Someone is already acting on that user. Please wait a moment and try again.")
        return
    _mod_busy.add(key)
    try:
        await _mod_do(interaction, is_kick, target_id, reason, me, delete_seconds)
    finally:
        _mod_busy.discard(key)


@bot.tree.command(name="ban", description="Ban a user from the server, even if they have left.")
@app_commands.describe(
    user="Pick a member as you type, or enter any Discord user ID (works for people who have left).",
    reason="Optional reason, saved in the audit log and the mod-log channel.",
)
@app_commands.default_permissions(ban_members=True)
@app_commands.checks.has_permissions(ban_members=True)
@app_commands.guild_only()
async def ban(
    interaction: discord.Interaction,
    # A text box with suggestions, not a User picker: the picker can't take the ID of someone who has left.
    user: app_commands.Range[str, 1, 100],
    reason: Optional[app_commands.Range[str, 1, 300]] = None,
):
    # Private ("Only you can see this"): errors and the result go only to the moderator; "banned" is posted in the channel.
    await interaction.response.defer(ephemeral=True)
    reason = reason.strip() if reason else None  # a blank reason counts as no reason
    await _mod_action(interaction, False, user, reason or None)


@ban.autocomplete("user")
async def ban_user_autocomplete(interaction: discord.Interaction, current: str) -> List[app_commands.Choice[str]]:
    return _user_choices(interaction, current, "ban_members")


@bot.tree.command(name="kick", description="Kick a member from the server.")
@app_commands.describe(
    user="Pick a member as you type, or enter the user ID of a current member.",
    reason="Optional reason, saved in the audit log and the mod-log channel.",
)
@app_commands.default_permissions(kick_members=True)
@app_commands.checks.has_permissions(kick_members=True)
@app_commands.guild_only()
async def kick(
    interaction: discord.Interaction,
    # A text box with suggestions, the same as /ban, so a member can also be kicked by their user ID.
    user: app_commands.Range[str, 1, 100],
    reason: Optional[app_commands.Range[str, 1, 300]] = None,
):
    # Private ("Only you can see this"): errors and the result go only to the moderator; "kicked" is posted in the channel.
    await interaction.response.defer(ephemeral=True)
    reason = reason.strip() if reason else None  # a blank reason counts as no reason
    await _mod_action(interaction, True, user, reason or None)


@kick.autocomplete("user")
async def kick_user_autocomplete(interaction: discord.Interaction, current: str) -> List[app_commands.Choice[str]]:
    return _user_choices(interaction, current, "kick_members")


# --------------------------------------------------------------------------
# /unverify
#
# The alternative to a kick for moderators who have Manage Roles but not Kick
# Members. It takes ALL of a member's roles away and gives them the Unverified
# role (UNVERIFIED_ROLE_ID) instead, so they can't see the server's channels any
# more. The person is chosen the same way as in /kick: type a name and pick from
# the suggestions, or enter the user ID of a current member.
#
# It asks first: a private question with a green Yes and a red No button. Nothing
# changes until Yes is pressed. Then every role is swapped in ONE request to
# Discord (so it either all happens or none of it does), the moderator gets the
# outcome as a new private message (the question is removed), and the change is
# written to the mod-log channel (MOD_LOG_CHANNEL_ID).
#
# Role safety: when the bot changes someone's roles, Discord only compares the
# BOT's highest role with the roles being changed. It never looks at the
# moderator's, so the bot makes those checks itself, the same ones /ban and
# /kick make. It refuses if the member owns the server, if their highest role is
# at or above the moderator's (the server owner may use it on anyone else), or
# if their highest role is at or above the bot's own. Roles that are managed by
# an integration (Server Booster, bot roles) can't be taken away by anyone, so
# they are left on the member.
# --------------------------------------------------------------------------

_UNVERIFY_CONFIRM_TIMEOUT = 60  # seconds the /unverify buttons stay usable
_UNVERIFY_FIELD_LIST_MAX = 900  # characters of role names put in one embed field (Discord allows 1024 per field)
_UNVERIFY_TEXT_LIST_MAX = 400   # characters of role names put in one plain message (Discord allows 2000 per message)


class _UnverifyPlan:
    """What /unverify would do to one member, worked out from how they are right now."""

    def __init__(
        self, member: discord.Member, unverified: discord.Role, to_remove: List[discord.Role],
        kept: List[discord.Role], name: str, safe: str,
    ) -> None:
        self.member = member
        self.unverified = unverified  # the role they end up with
        self.to_remove = to_remove    # every role that will be taken away, highest first
        self.kept = kept              # managed roles (Server Booster, bot roles): nobody can remove them, so they stay
        self.name = name              # the best name there is, as plain text
        self.safe = safe              # the same name made safe to put in a message (no pings, no formatting)


def _unverify_role_list(roles: List[discord.Role], limit: int) -> str:
    """Role names as plain text, separated by commas (no pings, no formatting). If they would be longer than `limit`
    characters the list is cut short and ends with something like "…and 3 more"."""
    names = [discord.utils.escape_markdown(discord.utils.escape_mentions(role.name)) for role in roles]
    for shown in range(len(names), 0, -1):  # the most names that fit
        text = ", ".join(names[:shown])
        if shown < len(names):
            text += f", …and {len(names) - shown} more"
        if len(text) <= limit:
            return text
    return f"…and {len(names)} more" if names else ""


async def _unverify_look(
    guild: discord.Guild, moderator: Any, me: discord.Member, target_id: int,
) -> Tuple[Optional[_UnverifyPlan], str]:
    """Look the member up, check everything, and work out what would change. Changes nothing.

    Returns (plan, "") if they can be unverified right now, otherwise (None, the private message that says why not).
    It runs when /unverify is used and again when Yes is pressed, because time has passed in between.
    """
    unverified = guild.get_role(UNVERIFIED_ROLE_ID)
    if unverified is None:
        return None, f"I couldn’t find the Unverified role (ID {UNVERIFIED_ROLE_ID}) in this server, so I haven’t changed anything."
    role_name = discord.utils.escape_markdown(unverified.name)
    if unverified.managed:
        return None, f"The **{role_name}** role is managed by an integration, so it can’t be given manually. I haven’t changed anything."
    if not me.top_role > unverified:
        return None, (
            f"My highest role isn’t above the **{role_name}** role, so Discord won’t let me give it. "
            "Please move my role above it (Server Settings → Roles). I haven’t changed anything."
        )

    # Ask Discord now (not a possibly stale copy): this decides which roles are taken away.
    try:
        member = await guild.fetch_member(target_id)
    except discord.NotFound:
        return None, "That user isn’t a member of this server, so they can’t be unverified."
    except discord.HTTPException:
        log.warning("/unverify: could not fetch %s from Discord", target_id)
        return None, "I couldn’t look that member up just now (Discord didn’t answer). Please try again in a moment."

    # The best name there is: the server nickname, otherwise their global display name or username.
    name = (member.display_name or "").strip() or f"User {target_id}"
    safe = discord.utils.escape_markdown(discord.utils.escape_mentions(name))

    # --- Is it allowed? The same checks as /ban and /kick (see the notes above). ----------------------
    if member.id == guild.owner_id:
        return None, f"I can’t unverify **{safe}** because they own the server. I haven’t changed anything."
    if moderator.id != guild.owner_id and not moderator.top_role > member.top_role:
        return None, f"You can’t unverify **{safe}** because their highest role is at or above yours. I haven’t changed anything."
    if not me.top_role > member.top_role:
        return None, (
            f"I can’t unverify **{safe}** because their highest role is at or above mine. "
            "Please move my role above theirs (Server Settings → Roles). I haven’t changed anything."
        )

    # --- What would change? Highest role first, and never @everyone (everybody has it). -----------------
    held = [role for role in reversed(member.roles) if not role.is_default()]
    kept = [role for role in held if role.managed]
    to_remove = [role for role in held if not role.managed and role.id != unverified.id]
    if not to_remove and _has_role(member, UNVERIFIED_ROLE_ID):
        return None, f"**{safe}** is already unverified, so I haven’t changed anything."
    return _UnverifyPlan(member, unverified, to_remove, kept, name, safe), ""


def _unverify_confirm_embed(plan: _UnverifyPlan, reason: Optional[str]) -> discord.Embed:
    """The private question /unverify asks: who, why, and exactly which roles would be taken away."""
    embed = _rem_embed(
        "Unverify this member?",
        f"Are you sure you want to unverify **{plan.safe}**?\n\n"
        f"This takes away **all** of their roles and gives them the **{discord.utils.escape_markdown(plan.unverified.name)}** "
        "role instead, so they lose access to everything those roles allowed.\n\n"
        "**Yes** does it. **No** does nothing.",
        0xE67E22,
    )
    embed.add_field(name="Member", value=_who(discord.utils.escape_mentions(plan.name), plan.member.id), inline=False)
    embed.add_field(
        name="Reason", value=discord.utils.escape_mentions(reason) if reason else "No reason provided", inline=False,
    )
    embed.add_field(
        name=f"Roles that will be removed ({len(plan.to_remove)})",
        value=_unverify_role_list(plan.to_remove, _UNVERIFY_FIELD_LIST_MAX) or "None",
        inline=False,
    )
    if plan.kept:
        embed.add_field(
            name="Roles that stay (managed by an integration, so nobody can remove them)",
            value=_unverify_role_list(plan.kept, _UNVERIFY_FIELD_LIST_MAX),
            inline=False,
        )
    embed.set_footer(
        text=f"Only you can see this. Nothing happens until you press Yes, and this expires after {_UNVERIFY_CONFIRM_TIMEOUT} seconds.",
    )
    return embed


def _unverify_audit_embed(plan: _UnverifyPlan, moderator: Any, reason: Optional[str]) -> discord.Embed:
    # Plain text only (names, never mentions): this embed must not ping or link anyone, so even a name that
    # contains something like <@123...> is broken up (escape_mentions) as well as having its formatting removed.
    name = discord.utils.escape_mentions(plan.name)
    moderator_name = discord.utils.escape_mentions(moderator.display_name)
    embed = discord.Embed(
        title="Member unverified",
        description=(
            f"**{discord.utils.escape_markdown(name)}** was unverified by "
            f"**{discord.utils.escape_markdown(moderator_name)}**. All of their roles were replaced with the "
            f"**{discord.utils.escape_markdown(plan.unverified.name)}** role."
        ),
        colour=discord.Colour(0xF39C12),
    )
    embed.add_field(name="Action", value="Unverify", inline=True)
    embed.add_field(name="Member", value=_who(name, plan.member.id), inline=True)
    embed.add_field(name="Moderator", value=_who(moderator_name, moderator.id), inline=True)
    embed.add_field(
        name="Reason", value=discord.utils.escape_mentions(reason) if reason else "No reason provided", inline=False,
    )
    embed.add_field(
        name=f"Roles removed ({len(plan.to_remove)})",
        value=_unverify_role_list(plan.to_remove, _UNVERIFY_FIELD_LIST_MAX) or "None",
        inline=False,
    )
    if plan.kept:
        embed.add_field(
            name="Roles kept (managed by an integration, so nobody can remove them)",
            value=_unverify_role_list(plan.kept, _UNVERIFY_FIELD_LIST_MAX),
            inline=False,
        )
    embed.timestamp = _utcnow()
    return embed


def _unverify_failure_text(safe: str, exc: BaseException) -> str:
    """The private message for an /unverify that Discord didn't carry out (no technical details)."""
    if _tkl_member_gone(exc):
        return f"**{safe}** is no longer in the server, so nothing was changed."
    if isinstance(exc, discord.Forbidden):
        return (
            f"Discord wouldn’t let me change **{safe}**’s roles. Please check that I have the **Manage Roles** permission "
            "and that my role is above theirs and above the Unverified role. Nothing was changed."
        )
    if _tkl_failed_cleanly(exc):
        return f"I couldn’t unverify **{safe}**: Discord returned an error ({getattr(exc, 'status', '?')}). Nothing was changed."
    # A timeout or server error: it may or may not have gone through, so nothing is logged.
    return (
        f"I couldn’t confirm whether **{safe}** was unverified, because Discord didn’t answer properly. "
        "Please check their roles in Discord before trying again. I haven’t logged anything."
    )


async def _unverify_conclude(interaction: discord.Interaction, text: str) -> None:
    """After Yes: show the moderator the outcome as a NEW private message, then remove the question they pressed Yes on.

    Never raises: by now the roles may already have been changed, and the moderator must still be told.
    """
    none = discord.AllowedMentions.none()
    text = text[:2000]  # Discord's limit for one message (the text is built to stay well below it)
    try:
        await interaction.followup.send(text, ephemeral=True, allowed_mentions=none)
    except Exception:
        log.warning("/unverify: could not send the result as a new private message; putting it in the question instead", exc_info=True)
        try:
            await interaction.edit_original_response(content=text, embed=None, view=None, allowed_mentions=none)
        except Exception:
            log.exception("/unverify: could not show the moderator the result")
        return
    try:
        await interaction.delete_original_response()
    except Exception:
        # Removing it is a nicety. If Discord won't, the question at least stops saying "Unverifying…".
        log.warning("/unverify: could not remove the question; replacing it with a short note instead", exc_info=True)
        try:
            await interaction.edit_original_response(
                content="The result is in the message below.", embed=None, view=None, allowed_mentions=none,
            )
        except Exception:
            log.warning("/unverify: could not update the question either", exc_info=True)


async def _unverify_do(
    interaction: discord.Interaction, guild: discord.Guild, me: discord.Member, target_id: int, reason: Optional[str],
) -> str:
    """Check everything again, take the roles away, then write it to the mod log. Returns the private message for the moderator.

    The question was asked a little while ago, so the member is looked up afresh and every check is made again.
    If the mod-log post fails the roles stay changed: it is added to the message as a warning.
    """
    moderator = interaction.user
    plan, problem = await _unverify_look(guild, moderator, me, target_id)
    if plan is None:
        return problem
    member, unverified, safe = plan.member, plan.unverified, plan.safe

    # The reason goes to Discord's audit log as well as the mod-log channel.
    audit_reason = f"Unverified by {moderator.display_name} ({moderator.id}) via /unverify: {reason or 'No reason provided'}"[:512]
    try:
        # One request replaces the whole list of roles, so it can't stop half way. The managed roles that nobody can
        # remove are part of the new list, which leaves them exactly as they are.
        updated = await member.edit(roles=[unverified] + plan.kept, reason=audit_reason)
    except Exception as exc:
        log.exception("/unverify: could not change the roles of %s (%s)", plan.name, target_id)
        return _unverify_failure_text(safe, exc)
    log.info(
        "/unverify: %s (%s) unverified by %s (%s) in guild %s; roles removed: %s",
        plan.name, target_id, moderator, moderator.id, guild.name,
        ", ".join(f"{role.name} ({role.id})" for role in plan.to_remove) or "none",
    )

    # --- The roles have changed. From here on a problem is only a warning for the moderator. ---------------
    warnings: List[str] = []
    if updated is not None:  # Discord sends the member back as it is now, so check that it is what was asked for
        now = [role for role in updated.roles if not role.is_default()]
        if {role.id for role in now} != {unverified.id} | {role.id for role in plan.kept}:
            warnings.append(
                f"⚠️ Discord accepted the change, but **{safe}** now has these roles: "
                f"{_unverify_role_list(list(reversed(now)), _UNVERIFY_TEXT_LIST_MAX) or 'none'}. "
                "That isn’t what I expected, so please check their roles in Discord."
            )

    problem = await _mod_log(guild, _unverify_audit_embed(plan, moderator, reason))
    if problem:
        warnings.append(
            f"⚠️ The roles were changed, but I couldn’t post it to the mod-log channel ({problem}). "
            "Please tell an admin; the details are in the bot’s logs."
        )

    given = f"the **{discord.utils.escape_markdown(unverified.name)}** role"
    if plan.to_remove:
        count = len(plan.to_remove)
        result = (
            f"✅ Unverified **{safe}** (`{target_id}`). I removed {count} role{'' if count == 1 else 's'} "
            f"({_unverify_role_list(plan.to_remove, _UNVERIFY_TEXT_LIST_MAX)}) and gave them {given}."
        )
    else:
        result = f"✅ Unverified **{safe}** (`{target_id}`). They had no roles to remove, so I just gave them {given}."
    if plan.kept:
        result += (
            " Managed roles can’t be removed by anyone, so I left these on them: "
            f"{_unverify_role_list(plan.kept, _UNVERIFY_TEXT_LIST_MAX)}."
        )
    return "\n".join([result] + warnings)


async def _unverify_go(interaction: discord.Interaction, target_id: int, reason: Optional[str]) -> None:
    """Yes was pressed: do it (see _unverify_do), then show the outcome. Nothing in here raises."""
    guild = interaction.guild
    assert guild is not None  # guaranteed by guild_only()
    try:
        me = guild.me
        key = _key(guild.id, target_id)
        if me is None or not me.guild_permissions.manage_roles:
            text = "I don’t have the **Manage Roles** permission, so I can’t change anyone’s roles. I haven’t changed anything."
        elif key in _mod_busy:
            text = "Someone is already acting on that user. Please wait a moment and try again."
        else:
            _mod_busy.add(key)
            try:
                text = await _unverify_do(interaction, guild, me, target_id, reason)
            finally:
                _mod_busy.discard(key)
    except Exception:
        log.exception("/unverify stopped unexpectedly (%s)", target_id)
        text = (
            "Something went wrong, so I can’t be sure what happened. "
            "Please check the member’s roles in Discord before trying again."
        )
    await _unverify_conclude(interaction, text)


class _UnverifyConfirmView(discord.ui.View):
    """The green Yes and red No buttons under the /unverify question. Only the moderator who ran /unverify can press them."""

    def __init__(self, interaction: discord.Interaction, target_id: int, reason: Optional[str], safe_name: str) -> None:
        super().__init__(timeout=_UNVERIFY_CONFIRM_TIMEOUT)
        self.command = interaction  # the /unverify command itself: its private reply IS the question, so it is edited if time runs out
        self.moderator = interaction.user
        self.target_id, self.reason, self.safe_name = target_id, reason, safe_name
        self._answered = False  # set by the first press of either button, so nothing can be processed twice

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.moderator.id:
            await interaction.response.send_message("Only the moderator who ran /unverify can use these buttons.", ephemeral=True)
            return False
        if not interaction.permissions.manage_roles:
            await interaction.response.send_message(
                "You no longer have the **Manage Roles** permission, so you can’t answer this.", ephemeral=True,
            )
            return False
        return True

    async def _answer(self, interaction: discord.Interaction, embed: discord.Embed) -> bool:
        """For the first press only: answer it straight away (Discord only waits 3 seconds) by taking the buttons away
        and showing `embed`. Returns False for any later press (a double tap, or the other button straight after).

        The view is deliberately not stopped. Until it times out by itself, a repeated tap is still acknowledged quietly;
        a stopped view would drop it and Discord would show "This interaction failed".
        """
        if self._answered:
            await interaction.response.defer()
            return False
        self._answered = True  # no await between the check and this line, so two presses can't both get through
        try:
            await interaction.response.edit_message(embed=embed, view=None)
        except Exception:
            self._answered = False  # Discord didn't take the press, so nothing has started: they can press again
            raise
        return True

    @discord.ui.button(label="Yes", style=discord.ButtonStyle.success)
    async def yes(self, interaction: discord.Interaction, button: discord.ui.Button) -> None:
        working = _rem_embed("Unverifying…", f"Unverifying **{self.safe_name}**. This only takes a moment.", 0xE67E22)
        if await self._answer(interaction, working):
            # Everything is looked up and checked again, because some time has passed since the question was asked.
            # The outcome then arrives as a new private message and this one is removed.
            await _unverify_go(interaction, self.target_id, self.reason)

    @discord.ui.button(label="No", style=discord.ButtonStyle.danger)
    async def no(self, interaction: discord.Interaction, button: discord.ui.Button) -> None:
        await self._answer(interaction, _rem_embed("Cancelled", "Nobody was unverified and no roles were changed.", 0x95A5A6))

    async def on_timeout(self) -> None:
        if self._answered:
            return
        self._answered = True
        try:
            await self.command.edit_original_response(embed=_rem_embed(
                "Timed out",
                "Nobody answered in time, so nobody was unverified and no roles were changed. "
                "Run /unverify again if you still want to do this.",
                0x95A5A6,
            ), view=None)
        except Exception:
            log.warning("/unverify: could not update the expired question", exc_info=True)

    async def on_error(self, interaction: discord.Interaction, error: Exception, item: discord.ui.Item) -> None:
        log.error("Unhandled error in the /unverify buttons", exc_info=error)
        text = (
            "Something went wrong with that button, so I can’t be sure what happened. "
            "Please check the member’s roles in Discord before trying again."
        )
        try:
            if interaction.response.is_done():
                await interaction.edit_original_response(content=text, embed=None, view=None)
            else:
                await interaction.response.send_message(text, ephemeral=True)
        except Exception:
            log.warning("/unverify: could not tell the user that a button failed", exc_info=True)


async def _unverify_start(interaction: discord.Interaction, user: str, reason: Optional[str]) -> None:
    """The checks before anyone is looked up, then the private Yes / No question. Changes nothing.
    The interaction has already been acknowledged."""
    guild = interaction.guild
    assert guild is not None  # guaranteed by guild_only()
    moderator = interaction.user

    async def reply(text: str) -> None:
        await _tkl_reply(interaction, text)  # private to the moderator

    target_id = _parse_user_id(user)
    if target_id is None:
        await reply(
            "That doesn’t look like a Discord user ID. Pick someone from the suggestions as you type, "
            "or enter their user ID (17 to 19 digits)."
        )
        return
    if target_id == moderator.id:
        await reply("You can’t unverify yourself.")
        return
    if bot.user is not None and target_id == bot.user.id:
        await reply("I can’t unverify myself.")
        return

    me = guild.me
    if me is None or not me.guild_permissions.manage_roles:
        await reply("I don’t have the **Manage Roles** permission, so I can’t change anyone’s roles. I haven’t changed anything.")
        return

    key = _key(guild.id, target_id)
    if key in _mod_busy:
        await reply("Someone is already acting on that user. Please wait a moment and try again.")
        return
    _mod_busy.add(key)
    try:
        plan, problem = await _unverify_look(guild, moderator, me, target_id)
        if plan is None:
            await reply(problem)
            return
        # Ask first, privately. Nothing is changed until Yes is pressed (see _UnverifyConfirmView).
        view = _UnverifyConfirmView(interaction, target_id, reason, plan.safe)
        await interaction.edit_original_response(
            embed=_unverify_confirm_embed(plan, reason), view=view, allowed_mentions=discord.AllowedMentions.none(),
        )
    finally:
        _mod_busy.discard(key)


@bot.tree.command(name="unverify", description="Take away all of a member's roles and give them the Unverified role.")
@app_commands.describe(
    user="Pick a member as you type, or enter the user ID of a current member.",
    reason="Optional reason, saved in the audit log and the mod-log channel.",
)
@app_commands.default_permissions(manage_roles=True)
@app_commands.checks.has_permissions(manage_roles=True)
@app_commands.guild_only()
async def unverify(
    interaction: discord.Interaction,
    # A text box with suggestions, the same as /kick, so a member can also be chosen by their user ID.
    user: app_commands.Range[str, 1, 100],
    reason: Optional[app_commands.Range[str, 1, 300]] = None,
):
    # Private ("Only you can see this"): the question, every error and the outcome go only to the moderator.
    await interaction.response.defer(ephemeral=True)
    reason = reason.strip() if reason else None  # a blank reason counts as no reason
    await _unverify_start(interaction, user, reason or None)


@unverify.autocomplete("user")
async def unverify_user_autocomplete(interaction: discord.Interaction, current: str) -> List[app_commands.Choice[str]]:
    return _user_choices(interaction, current, "manage_roles")


# --------------------------------------------------------------------------
# Timed-mute event listeners
#
# bot.listen() adds these IN ADDITION to the existing on_ready above, rather
# than replacing it. They need no extra intents: voice_states and members are
# already switched on.
# --------------------------------------------------------------------------


@bot.listen("on_ready")
async def timed_mutes_ready():
    try:
        await bot.mutes.on_ready()
    except Exception:
        log.exception("Timed-mute startup check failed")


@bot.listen("on_voice_state_update")
async def timed_mutes_voice(member: discord.Member, before: discord.VoiceState, after: discord.VoiceState):
    try:
        await bot.mutes.on_voice_update(member, before, after)
    except Exception:
        log.exception("Timed-mute voice handler failed")


@bot.listen("on_member_remove")
async def timed_mutes_member_removed(member: discord.Member):
    try:
        await bot.mutes.on_member_remove(member)
    except Exception:
        log.exception("Timed-mute member-removal handler failed")


# --------------------------------------------------------------------------
# /define and /urban
#
# /define looks words up in Merriam-Webster's Collegiate Dictionary API. Its key is read from the
# MERRIAM_WEBSTER_API_KEY environment variable each time the command is used and is never written in
# this file, so the bot starts normally without it: /define then just says it isn't set up. The key
# travels in the address of the request, so nothing here ever logs or shows an address or an error
# message from the network layer, only fixed wording.
#
# /urban only builds a link. It reads nothing from Urban Dictionary and needs no key.
# --------------------------------------------------------------------------

MERRIAM_WEBSTER_KEY_VAR = "MERRIAM_WEBSTER_API_KEY"
_MW_API_URL = "https://www.dictionaryapi.com/api/v3/references/collegiate/json/"
_MW_ENTRY_URL = "https://www.merriam-webster.com/dictionary/"
_MW_TIMEOUT = 6  # seconds Merriam-Webster gets for each step of the request (connecting, then answering)
_MW_TOTAL_TIMEOUT = 8  # seconds the command waits for the whole lookup before giving up
_MW_MAX_BYTES = 1_000_000  # a bigger reply is refused
_DEFINE_MAX_PARTS = 3  # blocks of definitions shown (one per part of speech), so the embed stays short on a phone
_DEFINE_MAX_MEANINGS = 3  # definitions shown in each block
_URBAN_SEARCH_URL = "https://www.urbandictionary.com/define.php"

_DEFINE_DOWN = "The dictionary isn’t working right now. Please try again later."
_DEFINE_UNREADABLE = "The dictionary sent back something I couldn’t read. Please try again later."

# Merriam-Webster's text has {markup} in it. A link token shows its first part ({sx|run||} shows "run").
_MW_LINK_TOKEN = re.compile(r"\{(?:a_link|d_link|i_link|et_link|mat|sx|dxt|ma)\|([^|}]*)[^}]*\}")
_MW_ANY_TOKEN = re.compile(r"\{[^{}]*\}")


class _DefineFailed(Exception):
    """A lookup that could not give a definition. `text` is what the person is told. The exception's own message goes
    only to the log, so it must never contain the API key or what the person typed."""

    def __init__(self, text: str, why: str) -> None:
        super().__init__(why)
        self.text = text


class _NoRedirects(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args: Any, **kwargs: Any) -> None:
        return None  # a redirect counts as an error, so the key is only ever sent to dictionaryapi.com


def _mw_request(url: str) -> Tuple[int, bytes]:
    """One GET to Merriam-Webster: the HTTP status and the body. It blocks, so it runs in a worker thread."""
    request = urllib.request.Request(url, headers={"Accept": "application/json", "User-Agent": "PossBot"})
    try:
        with urllib.request.build_opener(_NoRedirects).open(request, timeout=_MW_TIMEOUT) as response:
            return response.status, response.read(_MW_MAX_BYTES + 1)
    except urllib.error.HTTPError as error:  # 4xx and 5xx (and 3xx, as redirects are off) are still an answer
        with error:
            return error.code, error.read(_MW_MAX_BYTES + 1)


def _mw_clean(text: Any) -> str:
    """One of Merriam-Webster's strings as plain text: the {markup} is removed and a link keeps the words it shows."""
    if not isinstance(text, str):
        return ""
    text = _MW_LINK_TOKEN.sub(r"\1", text)
    for token, plain in (("{bc}", ": "), ("{ldquo}", "“"), ("{rdquo}", "”"), ("{amp}", "&")):
        text = text.replace(token, plain)
    return " ".join(_MW_ANY_TOKEN.sub("", text).split()).strip(": ")


def _mw_plain(text: Any) -> str:
    """Like _mw_clean, but also without the * that marks syllable breaks in a headword ("ag*o*nise")."""
    return _mw_clean(text).replace("*", "")


def _mw_key(text: Any) -> str:
    """The form used to compare words: plain, lower case, single spaces."""
    return " ".join(_mw_plain(text).lower().split())


def _mw_text(text: Any, limit: int) -> str:
    """Merriam-Webster text made safe to show in an embed (no pings, no stray formatting) and cut to `limit` characters."""
    text = discord.utils.escape_markdown(discord.utils.escape_mentions(_mw_clean(text)))
    return text if len(text) <= limit else text[: limit - 1].rstrip() + "…"


def _mw_senses(node: Any, found: Optional[List[Dict[str, Any]]] = None) -> List[Dict[str, Any]]:
    """Every sense (anything holding a "dt") inside part of an entry's "def", in order. Senses are nested several levels deep."""
    found = [] if found is None else found
    if isinstance(node, dict):
        if "dt" in node:
            found.append(node)
        for value in node.values():
            _mw_senses(value, found)
    elif isinstance(node, list):
        for value in node:
            _mw_senses(value, found)
    return found


def _mw_dt(sense: Dict[str, Any], kind: str) -> List[Any]:
    """The contents of a sense's "dt" items of one kind ("text" is the definition, "vis" the examples)."""
    items = sense.get("dt")
    return [item[1] for item in items if isinstance(item, list) and len(item) == 2 and item[0] == kind] if isinstance(items, list) else []


def _mw_meaning(sense: Dict[str, Any]) -> str:
    return " ".join(part for part in (_mw_clean(text) for text in _mw_dt(sense, "text")) if part)


def _mw_example(definition: Any) -> str:
    """The first example sentence ("verbal illustration") anywhere in a "def", or "" if there isn't one."""
    for sense in _mw_senses(definition):
        for examples in _mw_dt(sense, "vis"):
            for example in examples if isinstance(examples, list) else []:
                text = _mw_clean(example.get("t")) if isinstance(example, dict) else ""
                if text:
                    return text
    return ""


def _mw_match(entry: Dict[str, Any], wanted: str) -> Optional[Tuple[str, str, str, List[str], Any]]:
    """What one entry says about exactly the word or phrase asked for (already put through _mw_key): its name, part of
    speech, address on merriam-webster.com, definitions, and the part of the entry to look for an example in. None if
    the entry doesn't define it. A phrase like "take a stand" is only defined under another word ("stand"), as a "dro";
    the definitions of "stand" itself must never be shown for it."""
    meta = entry["meta"]
    hwi = entry["hwi"] if isinstance(entry.get("hwi"), dict) else {}
    headword = _mw_plain(hwi.get("hw"))
    entry_id = _mw_plain(str(meta.get("id", "")).split(":")[0])  # "run:2" is the second entry for "run"
    stems = meta.get("stems")
    stems = {_mw_key(stem) for stem in stems if isinstance(stem, str)} if isinstance(stems, list) else set()

    run_ons = entry.get("dros")
    for run_on in run_ons if isinstance(run_ons, list) else []:
        if isinstance(run_on, dict) and _mw_key(run_on.get("drp")) == wanted:
            phrase = _mw_plain(run_on.get("drp"))
            meanings = [_mw_meaning(sense) for sense in _mw_senses(run_on.get("def"))]
            return phrase, "phrase", phrase, [m for m in meanings if m], run_on.get("def")

    # A single word may match through an inflection ("ran" for "run"); a phrase must be the headword itself.
    if wanted in (_mw_key(headword), _mw_key(entry_id)) or (" " not in wanted and wanted in stems):
        shortdef = entry.get("shortdef")
        meanings = [_mw_clean(text) for text in shortdef] if isinstance(shortdef, list) else []
        return headword or entry_id or wanted, _mw_clean(entry.get("fl")), entry_id or headword, [m for m in meanings if m], entry.get("def")
    return None


def _mw_entry_link(*names: str) -> str:
    """The address of an entry on merriam-webster.com for the first name that can be written as an address of a sensible length."""
    for name in names:
        try:
            link = _MW_ENTRY_URL + urllib.parse.quote(name, safe="")
        except UnicodeError:  # text that can't be written as an address (a stray half of an emoji, say)
            continue
        if name and len(link) <= 1500:  # Discord refuses an embed link longer than 2048
            return link
    return _MW_ENTRY_URL


def _define_embed(term: str, data: Any) -> Tuple[Optional[discord.Embed], List[str]]:
    """Merriam-Webster's JSON in; out comes (embed, []) if the word is defined, or (None, similar spellings it
    suggests) if it isn't. Raises _DefineFailed if the reply isn't what the API documents."""
    if not isinstance(data, list):
        raise _DefineFailed(_DEFINE_UNREADABLE, "the reply was not a list")
    if all(isinstance(item, str) for item in data):  # [] for no match, or a list of similar spellings
        return None, [_mw_text(item, 60) for item in data[:5] if _mw_clean(item)]
    entries = [item for item in data if isinstance(item, dict) and isinstance(item.get("meta"), dict)]
    if not entries:
        raise _DefineFailed(_DEFINE_UNREADABLE, "the reply had no dictionary entries in it")

    wanted = _mw_key(term)
    blocks: List[Tuple[str, List[str]]] = []
    link_id, example = "", ""
    for entry in entries:
        match = _mw_match(entry, wanted)
        if match is None or not match[3] or len(blocks) >= _DEFINE_MAX_PARTS:
            continue
        name, part, link, meanings, source = match
        blocks.append((f"{name} — {part}" if part else name, meanings[:_DEFINE_MAX_MEANINGS]))
        link_id = link_id or link
        example = example or _mw_example(source)
    if not blocks:
        if not any(isinstance(entry.get("shortdef"), list) or isinstance(entry.get("dros"), list) for entry in entries):
            raise _DefineFailed(_DEFINE_UNREADABLE, "none of the entries had definitions in the expected place")
        return None, []

    link = _mw_entry_link(link_id, term)
    embed = discord.Embed(
        title=discord.utils.escape_mentions(term), url=link, colour=discord.Colour(0x3498DB),
        description=f"[Read the full entry on Merriam-Webster]({link})",
    )
    for name, meanings in blocks:
        shown = [_mw_text(meaning, 250) for meaning in meanings]
        embed.add_field(
            name=_mw_text(name, 100) or _mw_text(term, 100),
            value=shown[0] if len(shown) == 1 else "\n".join(f"**{number}.** {text}" for number, text in enumerate(shown, 1)),
            inline=False,
        )
    if example:
        embed.add_field(name="Example", value=f"*{_mw_text(example, 300)}*", inline=False)
    embed.set_footer(text="Source: Merriam-Webster’s Collegiate Dictionary")
    return embed, []


async def _define_lookup(term: str, key: str) -> Tuple[Optional[discord.Embed], List[str]]:
    """Asks Merriam-Webster about the word or phrase and returns what _define_embed returns. Raises _DefineFailed if the
    lookup fails, whatever the reason."""
    try:
        url = _MW_API_URL + urllib.parse.quote(term, safe="") + "?" + urllib.parse.urlencode({"key": key})
    except (UnicodeError, ValueError):
        raise _DefineFailed("I couldn’t look that up. Please try again using ordinary letters.", "the text could not be put into an address") from None
    try:
        status, body = await asyncio.wait_for(asyncio.get_running_loop().run_in_executor(None, _mw_request, url), _MW_TOTAL_TIMEOUT)
    except asyncio.TimeoutError:
        raise _DefineFailed("The dictionary took too long to answer. Please try again in a moment.", "timed out waiting for Merriam-Webster") from None
    except Exception as error:
        # Only the type of the error is kept: its message can contain the whole address, and the address contains the key.
        raise _DefineFailed(
            "I couldn’t reach the dictionary just now. Please try again in a moment.",
            f"could not reach Merriam-Webster ({type(error).__name__})",
        ) from None

    if status in (401, 403):
        raise _DefineFailed(_DEFINE_DOWN, f"Merriam-Webster refused the API key (HTTP {status})")
    if status == 429:
        raise _DefineFailed("The dictionary is busy right now. Please try again in a little while.", "Merriam-Webster is limiting requests (HTTP 429)")
    if status >= 500:
        raise _DefineFailed("The dictionary is having problems right now. Please try again later.", f"Merriam-Webster server error (HTTP {status})")
    if status in (400, 404):  # a complaint about the word itself, so there is nothing to define
        return None, []
    if status != 200 or len(body) > _MW_MAX_BYTES:
        raise _DefineFailed(_DEFINE_UNREADABLE, f"unexpected reply (HTTP {status}, {len(body)} bytes)")
    try:
        data = json.loads(body.decode("utf-8"))
    except ValueError:
        if b"invalid api key" in body.lower() or b"not subscribed" in body.lower():
            raise _DefineFailed(_DEFINE_DOWN, "Merriam-Webster refused the API key (it is invalid, or not for the Collegiate Dictionary)") from None
        raise _DefineFailed(_DEFINE_UNREADABLE, "the reply was not valid JSON") from None
    return _define_embed(term, data)


@bot.tree.command(name="define", description="Look up a word or phrase in the Merriam-Webster dictionary.")
@app_commands.describe(word_or_phrase="The word or phrase to look up.")
async def define(interaction: discord.Interaction, word_or_phrase: app_commands.Range[str, 1, 100]):
    none = discord.AllowedMentions.none()
    term = " ".join(word_or_phrase.split())  # no spaces at the ends, one space between words
    if not term:
        await interaction.response.send_message("Please type a word or phrase to look up.", ephemeral=True, allowed_mentions=none)
        return
    key = os.environ.get(MERRIAM_WEBSTER_KEY_VAR, "").strip()
    if not key:
        log.warning("/define was used, but the %s environment variable is not set.", MERRIAM_WEBSTER_KEY_VAR)
        await interaction.response.send_message("Dictionary lookups aren’t set up on this bot yet.", ephemeral=True, allowed_mentions=none)
        return

    # A lookup can take a few seconds and Discord only waits 3 for a first answer, so say "working on it" first.
    await interaction.response.defer()
    try:
        embed, suggestions = await _define_lookup(term, key)
    except _DefineFailed as failure:
        log.warning("/define: %s", failure)
        await interaction.followup.send(failure.text, allowed_mentions=none)
        return
    except Exception as error:
        # Where it broke is logged, but not the error's own message: the one place a key or a typed word could turn up.
        log.error("/define: unexpected %s while looking a word up:\n%s", type(error).__name__, "".join(traceback.format_tb(error.__traceback__)).rstrip())
        await interaction.followup.send("Something went wrong looking that up.", allowed_mentions=none)
        return

    if embed is None:
        text = f"I couldn’t find a definition for **{discord.utils.escape_markdown(discord.utils.escape_mentions(term))}**."
        if suggestions:
            text += " Did you mean: " + ", ".join(suggestions) + "?"
        await interaction.followup.send(text, allowed_mentions=none)
        return
    await interaction.followup.send(embed=embed, allowed_mentions=none)


def _urban_url(term: str) -> str:
    """Urban Dictionary's own search address for the term, with every space, symbol and non-English character percent-encoded."""
    return _URBAN_SEARCH_URL + "?" + urllib.parse.urlencode({"term": term})


# No NSFW check, no channel check and no permission check on purpose: this has to work in every channel, like the
# Carl-bot tag it replaces. Nothing here (or in the bot's setup) marks a command as age-restricted.
@bot.tree.command(name="urban", description="Get an Urban Dictionary definition for a word or phrase.")
@app_commands.describe(word_or_phrase="The word or phrase to look up.")
async def urban(interaction: discord.Interaction, word_or_phrase: app_commands.Range[str, 1, 100]):
    none = discord.AllowedMentions.none()
    term = " ".join(word_or_phrase.split())  # no spaces at the ends, one space between words
    try:
        url = _urban_url(term) if term else None
    except (UnicodeError, ValueError):  # text that can't be written as an address (a stray half of an emoji, say)
        url = None
    if url is None:
        await interaction.response.send_message(
            "I couldn’t make a link from that. Please type a word or phrase using ordinary characters.",
            ephemeral=True, allowed_mentions=none,
        )
        return
    # The address goes in as plain text so Discord may show its usual website preview; nothing depends on it appearing.
    shown = discord.utils.escape_markdown(discord.utils.escape_mentions(term))
    await interaction.response.send_message(f"Urban Dictionary search for **{shown}**:\n{url}", allowed_mentions=none)


# --------------------------------------------------------------------------
# ESO server-status observer (observe-only)
#
# This is NOT the server-status monitor. It announces nothing and pings nobody. All it does is look at
# https://esoserverstatus.net/ every couple of minutes and write down what it sees: the reply's headers, the row
# for each megaserver, and the page's own HTML around those rows. That evidence goes to ONE channel in the private
# test server (ESO_OBSERVER_CHANNEL_ID) and to the log, so the real monitor can later be built on what the page
# really does -- including what it shows when a server is down or in maintenance -- instead of on guesses.
# It keeps no file, so there is nothing to collect from the host.
#
# It is made to fail quietly: a slow or broken site, an odd page or an unusable channel only ever produces a log
# line (and, for a site that keeps failing, one notice in the test channel). It touches no command and nothing else
# in the bot.
# --------------------------------------------------------------------------

_ESO_URL = "https://esoserverstatus.net/"
_ESO_HOSTS = ("esoserverstatus.net", "www.esoserverstatus.net")  # a redirect may only lead to one of these...
_ESO_SCHEMES = ("https",)  # ...over https
_ESO_USER_AGENT = "PossBot/1.0 (Discord bot; read-only ESO status observer; one request every 2 minutes or so)"
_ESO_TIMEOUT = 10  # seconds the site gets for each step of a request
_ESO_TOTAL_TIMEOUT = 25  # seconds for a whole check, reading the page included
_ESO_MAX_BYTES = 2_000_000  # a bigger page is cut off here
_ESO_FAILS_BEFORE_NOTICE = 3  # failed checks in a row before a notice is posted
_ESO_HEARTBEAT = 6 * 3600  # seconds between "still watching" lines
_ESO_MESSAGE_LIMIT = 1900  # characters in one message (Discord's limit is 2000)
_ESO_POSTS_PER_HOUR = 24  # the most messages posted in an hour, however much changes
_ESO_REPORT_MESSAGES = 4  # the most messages one capture may take
_ESO_MIN_SECTION = 450  # characters; when a capture has to be shortened, no section is cut below this
_ESO_SLEEP_SLICE = 5  # seconds; the observer sleeps in slices this long so it notices at once that the bot is closing
_ESO_HEADERS = (
    "date", "age", "cache-control", "expires", "last-modified", "etag", "server", "content-type", "content-length",
    "content-encoding", "vary", "location", "retry-after", "cf-cache-status", "x-cache", "via",
)  # the only reply headers that are recorded
_ESO_STATUS_WORDS = re.compile(
    r"(?i)\b(operational|outage|degraded|maintenance|offline|online|down|disrupt\w*|issues?|partial|unavailable|unknown|restor\w*)\b"
)
_ESO_HINTS = (
    "fetch(", "xmlhttprequest", "axios", "$.ajax", "$.get", "getjson", "eventsource", "websocket", "/api/", ".json",
    "setinterval", "location.reload", "last updated", "lastupdated", "last_updated",
)  # words that, inside the page's own scripts, would show where the status really comes from
_ESO_TAG = re.compile(r"<[^<>]*>")
_ESO_TAG_NAME = re.compile(r"<(/?)\s*([A-Za-z][A-Za-z0-9:-]*)")
_ESO_SRC = re.compile(r"""(?i)\bsrc\s*=\s*["']?([^"'\s>]+)""")
_ESO_LONG_VALUE = re.compile(r'(=\s*")([^"]{70,})(")')


class _EsoFetchError(Exception):
    """A check that got no usable answer. `kind` is a short plain description; it never contains an address."""

    def __init__(self, kind: str, reply: Optional["_EsoReply"] = None) -> None:
        super().__init__(kind)
        self.kind = kind
        self.reply = reply


class _EsoReply:
    """What came back from one request: the status, the few headers worth recording, and the page itself."""

    def __init__(
        self, status: int, headers: Dict[str, str], body: bytes, url: str, ms: int, cut: bool, cookies: bool, charset: str,
    ) -> None:
        self.status, self.headers, self.body, self.url = status, headers, body, url
        self.ms, self.cut, self.cookies, self.charset = ms, cut, cookies, charset

    @property
    def text(self) -> str:
        try:
            return self.body.decode(self.charset, errors="replace")
        except LookupError:  # a character set Python doesn't know
            return self.body.decode("utf-8", errors="replace")


class _EsoView:
    """What one reading of the page held, in the pieces the report needs (see _eso_analyse)."""

    def __init__(self) -> None:
        self.rows: List[str] = []  # one line per megaserver, e.g. "XBOX EU Megaserver | Online"
        self.how = "nothing found"  # how the rows were found
        self.banner: List[str] = []  # other short status-like lines, e.g. "All Systems Operational"
        self.title = ""
        self.head = ""  # the start of the page's text, for when no rows can be found
        self.tables: List[str] = []  # the HTML of the tables that mention Xbox
        self.windows: List[str] = []  # the HTML around other mentions of Xbox
        self.in_scripts: List[str] = []  # mentions of Xbox inside the page's scripts
        self.updated: List[str] = []  # the HTML around "last updated" and any <time> tag
        self.script_srcs: List[str] = []
        self.metas: List[str] = []
        self.hints: List[str] = []

    @property
    def signature(self) -> Tuple[Tuple[str, ...], Tuple[str, ...]]:
        """What counts as 'the page changed': the rows and the banner, with numbers ignored so a clock or a counter
        on the page can't make every check look like a change."""
        return (
            tuple(re.sub(r"\d+", "#", row) for row in self.rows),
            tuple(re.sub(r"\d+", "#", line) for line in self.banner),
        )


class _EsoRedirects(urllib.request.HTTPRedirectHandler):
    max_redirections = 3

    def redirect_request(self, req: Any, fp: Any, code: int, msg: str, headers: Any, newurl: str) -> Any:
        target = urllib.parse.urlsplit(newurl)
        if target.scheme not in _ESO_SCHEMES or (target.hostname or "").lower() not in _ESO_HOSTS:
            return None  # anywhere else counts as a failed check, not something to follow
        return super().redirect_request(req, fp, code, msg, headers, newurl)


def _eso_error_kind(error: BaseException) -> str:
    """A short plain description of why a request failed. Only the kind of error is used, never its message."""
    reason = getattr(error, "reason", None)  # a URLError carries the real cause here
    if not isinstance(reason, BaseException):
        if isinstance(error, urllib.error.URLError):
            return "connection problem"
        reason = error
    name = type(reason).__name__
    if isinstance(reason, TimeoutError) or name == "timeout":
        return "timed out"
    if "SSL" in name or "Certificate" in name:
        return "TLS/certificate problem"
    if name == "gaierror":
        return "the name could not be looked up (DNS)"
    if isinstance(reason, ConnectionRefusedError):
        return "connection refused"
    if isinstance(reason, (ConnectionResetError, ConnectionAbortedError, BrokenPipeError)) or name in (
        "IncompleteRead", "RemoteDisconnected", "BadStatusLine",
    ):
        return "connection dropped"
    if isinstance(reason, OSError):
        return "could not connect"
    return "connection problem"


def _eso_read(response: Any, status: int, started: float) -> _EsoReply:
    """Read the body (up to the size limit and the overall time limit) and note the headers worth keeping."""
    deadline = started + _ESO_TOTAL_TIMEOUT - 3
    chunks: List[bytes] = []
    size, cut = 0, False
    take = getattr(response, "read1", response.read)  # read1 returns what has arrived, so a site that trickles can't hold this up
    while True:
        if time.monotonic() > deadline:
            raise _EsoFetchError("timed out")
        chunk = take(65536)
        if not chunk:
            break
        chunks.append(chunk)
        size += len(chunk)
        if size > _ESO_MAX_BYTES:
            cut = True
            break
    message = response.headers
    promised = message.get("content-length")
    if not cut and promised is not None and promised.strip().isdigit() and size < int(promised):
        raise _EsoFetchError("connection dropped")  # the site hung up before the whole page arrived
    headers: Dict[str, str] = {}
    for name in _ESO_HEADERS:
        value = message.get(name)
        if value:
            headers[name] = " ".join(str(value).split())[:120]
    return _EsoReply(
        status, headers, b"".join(chunks)[:_ESO_MAX_BYTES], response.geturl(), int((time.monotonic() - started) * 1000), cut,
        message.get("set-cookie") is not None, message.get_content_charset() or "utf-8",
    )


def _eso_request() -> _EsoReply:
    """One GET of the status page. It blocks, so it runs in a worker thread."""
    started = time.monotonic()
    request = urllib.request.Request(_ESO_URL, headers={
        "User-Agent": _ESO_USER_AGENT,
        "Accept": "text/html,application/xhtml+xml;q=0.9,*/*;q=0.5",
        "Accept-Encoding": "identity",
    })
    try:
        with urllib.request.build_opener(_EsoRedirects).open(request, timeout=_ESO_TIMEOUT) as response:
            return _eso_read(response, response.status, started)
    except urllib.error.HTTPError as error:  # 4xx, 5xx and a refused redirect are still an answer worth recording
        with error:
            return _eso_read(error, error.code, started)
    except _EsoFetchError:
        raise
    except Exception as error:
        raise _EsoFetchError(_eso_error_kind(error)) from None


def _eso_lower(text: str) -> str:
    """Lower case that keeps every character where it was, so a position found in this text is also the position in the
    original (the capital dotted I is the one letter whose lower case would be two characters long)."""
    return text.replace("\u0130", "i").lower()


def _eso_text(text: str) -> str:
    """Text taken from the page: character references decoded and every run of white space made one space."""
    return " ".join(html.unescape(text).split())


def _eso_scan(page: str) -> Tuple[List[str], List[Tuple[int, int]], List[str], List[str]]:
    """Read the page once. Gives back its text as separate pieces (a new piece starts at every tag), where the
    <script> and <style> bodies are, the addresses of the scripts it loads, and its <meta> tags. It is a single
    pass with no nested searching, so a damaged or hostile page can't make it slow."""
    pieces: List[str] = []
    code: List[Tuple[int, int]] = []
    sources: List[str] = []
    metas: List[str] = []
    lowered = _eso_lower(page)
    pos, size = 0, len(page)
    while pos < size:
        tag = _ESO_TAG.search(page, pos)
        if tag is None:
            pieces.append(page[pos:])
            break
        if tag.start() > pos:
            pieces.append(page[pos:tag.start()])
        pos = tag.end()
        named = _ESO_TAG_NAME.match(tag.group())
        if named is None or named.group(1):  # not a tag with a name, or a closing tag
            continue
        name = named.group(2).lower()
        if name == "meta" and len(metas) < 12:
            metas.append(tag.group())
        elif name in ("script", "style") and not tag.group().endswith("/>"):
            if name == "script":
                source = _ESO_SRC.search(tag.group())
                if source is not None and len(sources) < 25:
                    sources.append(source.group(1)[:150])
            end = lowered.find("</" + name, pos)
            end = size if end < 0 else end
            code.append((pos, end))
            pos = end
    return [token for token in (_eso_text(piece) for piece in pieces) if token], code, sources, metas


def _eso_rows(tokens: List[str]) -> Tuple[List[str], str]:
    """One line per megaserver label, with whatever text follows it (the status). If no label says "megaserver",
    any short piece of text mentioning Xbox is used instead; if there is none, no rows are found."""
    every = [i for i, token in enumerate(tokens) if len(token) <= 60 and "megaserver" in token.lower()]
    xbox_labels = [i for i in every if "xbox" in tokens[i].lower()]
    labels = sorted(set(every[:60]) | set(xbox_labels[:60]))  # a page with a great many gets its first 60 and its Xbox ones
    how = "megaserver labels"
    if not labels:
        labels = [i for i, token in enumerate(tokens) if len(token) <= 60 and "xbox" in token.lower()][:6]
        how = "any text mentioning xbox"
    rows: List[str] = []
    for i in labels:
        parts = [tokens[i]]
        for token in tokens[i + 1:i + 3]:
            if "megaserver" in token.lower():
                break
            parts.append(token[:60])
        rows.append(" | ".join(parts))
    return rows, (how if rows else "nothing found")


def _eso_banner(tokens: List[str], rows: List[str]) -> List[str]:
    """Lines elsewhere on the page that talk about status ("All Systems Operational", "Partial outage", a notice that
    maintenance is planned...). A line longer than 160 characters is shortened."""
    used = {part for row in rows for part in row.split(" | ")}
    found: List[str] = []
    for token in tokens:
        short = token[:160]
        if token not in used and short not in found and (_ESO_STATUS_WORDS.search(token) or token.lower() == "up"):
            found.append(short)
            if len(found) == 8:
                break
    return found


def _eso_positions(lowered: str, needle: str, limit: int) -> List[int]:
    found: List[int] = []
    start = 0
    while len(found) < limit:
        at = lowered.find(needle, start)
        if at < 0:
            break
        found.append(at)
        start = at + len(needle)
    return found


def _eso_merge(spans: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    merged: List[Tuple[int, int]] = []
    for start, end in sorted(spans):
        if merged and start <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(merged[-1][1], end))
        else:
            merged.append((start, end))
    return merged


def _eso_focus(fragment: str) -> str:
    """A table with one row to a line, cut down to its first line and the lines that mention Xbox (each with the line
    before and after), so a long table still shows the rows that matter."""
    rows = fragment.split("\n")
    keep = {0}
    for number, row in enumerate(rows):
        if "xbox" in row.lower():
            keep.update((number - 1, number, number + 1))
    out: List[str] = []
    skipped = 0
    for number, row in enumerate(rows):
        if number in keep:
            if skipped:
                out.append(f"…[{skipped} line{'s' if skipped != 1 else ''} left out]")
                skipped = 0
            out.append(row)
        else:
            skipped += 1
    if skipped:
        out.append(f"…[{skipped} line{'s' if skipped != 1 else ''} left out]")
    return "\n".join(out)


def _eso_squeeze(fragment: str, limit: int, lines: bool = False, focus: int = 0) -> str:
    """HTML shortened so it is easy to read on a phone: pictures (<svg>) and very long attribute values are cut
    down, white space is collapsed and, for a table, each row starts on its own line. With `focus`, a table longer
    than that is cut down to the lines that mention Xbox (see _eso_focus). Nothing else is changed."""
    fragment = fragment[:30000]
    lowered = _eso_lower(fragment)
    out: List[str] = []
    pos = 0
    while True:
        start = lowered.find("<svg", pos)
        end = lowered.find("</svg>", start) if start >= 0 else -1
        if start < 0 or end < 0:
            out.append(fragment[pos:])
            break
        out.append(fragment[pos:start])
        out.append("<svg…/>")
        pos = end + 6
    fragment = _ESO_LONG_VALUE.sub(lambda m: m.group(1) + m.group(2)[:30] + "…" + m.group(3), "".join(out))
    fragment = re.sub(r">\s+<", "><", re.sub(r"\s+", " ", fragment)).strip()
    if lines:
        fragment = re.sub(r"(?i)(<(?:/?table|/?thead|/?tbody|tr)\b)", r"\n\1", fragment).strip()
        if focus and len(fragment) > focus:
            fragment = _eso_focus(fragment)
    if len(fragment) > limit:
        fragment = fragment[:limit] + f" …[{len(fragment) - limit:,} more characters]"
    return fragment


def _eso_analyse(page: str) -> _EsoView:
    """Pick out of the page everything the report needs. It assumes nothing about how the page is built: the rows
    are found by their words, and the HTML around them is passed on exactly so it can be studied."""
    view = _EsoView()
    tokens, code, view.script_srcs, view.metas = _eso_scan(page)
    lowered = _eso_lower(page)
    view.rows, view.how = _eso_rows(tokens)
    view.banner = _eso_banner(tokens, view.rows)
    view.head = " | ".join(tokens)[:600]
    title = re.search(r"(?is)<title\b[^>]*>(.*?)</title", page[:30000])
    view.title = _eso_text(title.group(1))[:100] if title else ""

    tables: List[Tuple[int, int]] = []
    windows: List[Tuple[int, int]] = []
    in_scripts: List[Tuple[int, int]] = []
    body_at = lowered.find("<body")
    for pos in _eso_positions(lowered, "xbox", 40):
        if any(start <= pos < end for start, end in code):
            in_scripts.append((max(0, pos - 250), min(len(page), pos + 350)))
            continue
        if 0 <= body_at and pos < body_at:  # the title and the meta tags above <body> are not rows
            continue
        start = lowered.rfind("<table", 0, pos)
        end = lowered.find("</table", pos)
        if start >= 0 and end >= 0 and lowered.rfind("</table", start, pos) < 0 and end - start <= 40000:
            span = (start, min(len(page), end + 8))
            if span not in tables:
                tables.append(span)
        else:
            windows.append((max(0, pos - 300), min(len(page), pos + 500)))
    view.tables = [_eso_squeeze(page[a:b], 5000, lines=True, focus=2000) for a, b in tables[:3]]
    view.windows = [_eso_squeeze(page[a:b], 1200) for a, b in _eso_merge(windows)[:3]]
    view.in_scripts = [_eso_squeeze(page[a:b], 900) for a, b in _eso_merge(in_scripts)[:3]]

    updated: List[Tuple[int, int]] = []
    for needle in ("last updated", "last-updated", "last_updated", "lastupdated"):
        at = lowered.find(needle)
        if at >= 0:
            updated.append((max(0, at - 200), min(len(page), at + 400)))
            break
    updated.extend((at, min(len(page), at + 250)) for at in _eso_positions(lowered, "<time", 2))
    view.updated = [_eso_squeeze(page[a:b], 900) for a, b in _eso_merge(updated)[:3]]

    taken: List[Tuple[int, int]] = []
    for start, end in code:
        body = lowered[start:end]
        if len(body) < 20:
            continue
        for needle in _ESO_HINTS:
            at = body.find(needle)
            if at < 0 or len(view.hints) >= 8:
                continue
            first, last = max(start, start + at - 110), min(end, start + at + 160)
            if any(a < last and first < b for a, b in taken):
                continue
            taken.append((first, last))
            view.hints.append(_eso_squeeze(page[first:last], 300))
    return view


def _eso_check() -> Tuple[_EsoReply, Optional[_EsoView]]:
    """One whole check, run in a worker thread: fetch the page and, if it came back fine, analyse it."""
    reply = _eso_request()
    if reply.status != 200:
        return reply, None
    if reply.headers.get("content-encoding", "identity").lower() not in ("", "identity"):
        raise _EsoFetchError("the page came back compressed, which was not asked for", reply)
    return reply, _eso_analyse(reply.text)


# ----- turning a reading into Discord messages ------------------------------------------------------------

def _eso_when(moment: Optional[datetime] = None) -> str:
    return (moment or _utcnow()).strftime("%Y-%m-%d %H:%M:%S UTC")


def _eso_facts(reply: Optional[_EsoReply], view: Optional[_EsoView]) -> str:
    lines: List[str] = []
    if reply is not None:
        lines.append(f"status: {reply.status}   bytes: {len(reply.body):,}{' (cut off)' if reply.cut else ''}   time: {reply.ms} ms")
        lines.append(f"url: {reply.url[:150]}")
        lines.extend(f"{name}: {reply.headers[name]}" for name in _ESO_HEADERS if name in reply.headers)
        lines.append("sets a cookie: " + ("yes" if reply.cookies else "no"))
    if view is not None:
        lines.append(f"title: {view.title or '(none)'}")
        banner = " | ".join(view.banner)
        lines.append("banner: " + ((banner[:400] + "…") if len(banner) > 400 else banner or "(none)"))
        lines.append(f"rows (found by: {view.how}):")
        chosen = {number for number, row in enumerate(view.rows) if "xbox" in row.lower()}  # the Xbox rows always, then the others in page order
        for number in range(len(view.rows)):
            if len(chosen) >= 14:
                break
            chosen.add(number)
        lines.extend(f"  {view.rows[number]}" for number in sorted(chosen))
        if len(view.rows) > len(chosen):
            lines.append(f"  …and {len(view.rows) - len(chosen)} more rows")
        if not view.rows:
            lines.append("  (none)")
        refresh = [meta for meta in view.metas if "refresh" in meta.lower()]
        lines.append("meta refresh: " + (refresh[0][:200] if refresh else "none"))
    return "\n".join(lines)


def _eso_diff(old: _EsoView, new: _EsoView) -> str:
    lines: List[str] = []
    for label, before, after in (("row", old.rows, new.rows), ("banner", old.banner, new.banner)):
        lines.extend(f"- {label}: {item}" for item in before if item not in after)
        lines.extend(f"+ {label}: {item}" for item in after if item not in before)
    if not lines:
        lines.append("(the same lines, in a different order)")
    changed = [row for row in old.rows if "xbox" in row.lower()] != [row for row in new.rows if "xbox" in row.lower()]
    lines.append("Xbox rows changed: " + ("yes" if changed else "no"))
    return "\n".join(lines)


def _eso_head(reply: _EsoReply) -> str:
    """The start of a reply, for when the page can't be understood (an error page, a 'checking your browser' page...)."""
    return _eso_squeeze(reply.text[:3000], 700)


def _eso_split(text: str, room: int) -> List[str]:
    parts: List[str] = []
    while len(text) > room:
        cut = text.rfind("\n", 0, room)
        if cut < room // 2:
            cut = text.rfind(" ", 0, room)
        if cut < room // 2:
            cut = room
        parts.append(text[:cut].rstrip())
        text = text[cut:].lstrip("\n ")
    if text:
        parts.append(text)
    return parts


def _eso_fit(sections: List[Tuple[str, str]], budget: int) -> List[Tuple[str, str]]:
    """The sections shortened, longest first, until together they hold at most `budget` characters. Every section
    keeps at least _ESO_MIN_SECTION characters, so a long one can't push the others out of the report."""
    limits = [len(body) for _, body in sections]
    while sum(limits) > budget:
        longest = max(range(len(limits)), key=limits.__getitem__)
        if limits[longest] <= _ESO_MIN_SECTION:
            break
        limits[longest] = max(_ESO_MIN_SECTION, limits[longest] - max(40, (sum(limits) - budget) // 2))
    fitted: List[Tuple[str, str]] = []
    for (heading, body), limit in zip(sections, limits):
        if len(body) > limit:
            body = body[:limit].rstrip() + f" …[{len(body) - limit:,} more characters]"
        fitted.append((heading, body))
    return fitted


def _eso_pack(lead: str, sections: List[Tuple[str, str]]) -> List[str]:
    """A short lead line and (heading, body) sections as Discord messages of at most _ESO_MESSAGE_LIMIT characters.
    Every body goes in a code block, so Discord shows it exactly and it copies in one go; a long body is split over
    several blocks."""
    blocks: List[str] = []
    for heading, body in sections:
        body = re.sub(r"`(?=``)", "`\u200b", body.strip("\n"))  # no run of three backticks survives, so the page can't close the block early
        for number, part in enumerate(_eso_split(body, _ESO_MESSAGE_LIMIT - len(heading) - 30), 1):
            title = heading if number == 1 else f"{heading} (part {number})"
            blocks.append(f"**{title}**\n```\n{part}\n```")
    messages: List[str] = []
    current = lead
    for block in blocks:
        if current and len(current) + 1 + len(block) > _ESO_MESSAGE_LIMIT:
            messages.append(current)
            current = block
        else:
            current = f"{current}\n{block}" if current else block
    if current:
        messages.append(current)
    return messages


def _eso_messages(lead: str, sections: List[Tuple[str, str]]) -> List[str]:
    """_eso_pack, limited to _ESO_REPORT_MESSAGES messages; anything beyond that is left out (and the last message says so)."""
    messages = _eso_pack(lead, sections)
    if len(messages) > _ESO_REPORT_MESSAGES:
        left_out = sum(len(message) for message in messages[_ESO_REPORT_MESSAGES:])
        messages = messages[:_ESO_REPORT_MESSAGES] + [f"…{left_out:,} more characters were left out to keep this short."]
    return messages


def _eso_capture(
    lead: str, reply: _EsoReply, view: _EsoView, full: bool, changes: str = "", extra: Tuple[Tuple[str, str], ...] = (),
) -> List[str]:
    """The messages for a reading: what changed (if anything), the facts, then the page's own HTML around the rows.
    A first capture also lists the page's scripts and anything in them that hints where the status comes from."""
    sections: List[Tuple[str, str]] = []
    if changes:
        sections.append(("What changed", changes))
    sections.append(("Facts", _eso_facts(reply, view)))
    sections.extend(extra)
    if full and view.head and not any(heading.startswith("Start of the page") for heading, _ in extra):
        sections.append(("Start of the page's text", view.head[:400]))
    if view.tables:
        sections.append(("Table HTML", "\n\n".join(view.tables)))
    if view.windows:
        sections.append(("Other HTML around \"xbox\"", "\n\n".join(view.windows)))
    if full:  # the page's scripts come before the rest: they are what shows where the status really comes from
        extras = ["scripts it loads:"] + [f"  {src}" for src in view.script_srcs[:12]]
        extras += ["", "meta tags:"] + [f"  {meta[:200]}" for meta in view.metas[:8]]
        if view.hints:
            extras += ["", "hints in its own scripts:"] + [f"  {hint}" for hint in view.hints]
        sections.append(("Scripts and hints", "\n".join(extras)))
        if view.in_scripts:
            sections.append(("\"xbox\" inside the page's scripts or styles", "\n\n".join(view.in_scripts)))
    if view.updated:
        sections.append(("HTML around \"last updated\"", "\n\n".join(view.updated)))
    budget = 6000  # characters of evidence; if that doesn't pack into few enough messages, the longest sections are cut further
    while True:
        fitted = _eso_fit(sections, budget)
        if len(_eso_pack(lead, fitted)) <= _ESO_REPORT_MESSAGES or budget <= 1500:
            return _eso_messages(lead, fitted)
        budget = budget * 3 // 4


# ----- the observer itself ----------------------------------------------------------------------------------

class _EsoObserver:
    """Checks the page every `interval` seconds and reports: the first good reading, every change after it, a site
    that keeps failing (once, and again when it recovers) and a 'still watching' line every few hours. Everything it
    keeps is in memory, so a restart simply makes a fresh first capture."""

    def __init__(self, client: commands.Bot, interval: float) -> None:
        self.bot = client
        self.interval = interval
        self.fails = 0  # checks in a row that failed
        self.failed_total = 0
        self.ok_total = 0
        self.failure_since: Optional[datetime] = None
        self.failure_noticed = False
        self.state = ""  # "" before the first good reading, then "ok" or "no rows"
        self.last_view: Optional[_EsoView] = None  # the last reading that had rows
        self.last_change: Optional[datetime] = None
        self.sent: List[float] = []  # when each recent message was posted (monotonic seconds)
        self.held_back = 0
        self.problem = ""  # why the channel can't be used, so each reason is logged once
        self.last_beat = time.monotonic()

    # ----- where it posts ---------------------------------------------------

    def _unusable(self, why: str) -> None:
        if why != self.problem:
            self.problem = why
            log.warning("ESO observer: not posting to Discord, only to the log: %s", why)
        return None

    async def _channel(self) -> Optional[discord.TextChannel]:
        """The test channel if it can be used right now, otherwise None. This is the only place the observer ever posts."""
        if not ESO_OBSERVER_CHANNEL_ID:
            return self._unusable("no channel is set (ESO_OBSERVER_CHANNEL_ID is 0)")
        channel = self.bot.get_channel(ESO_OBSERVER_CHANNEL_ID)
        if channel is None:
            try:
                channel = await self.bot.fetch_channel(ESO_OBSERVER_CHANNEL_ID)
            except discord.NotFound:
                return self._unusable("the channel no longer exists")
            except discord.Forbidden:
                return self._unusable("I don't have access to the channel")
            except discord.HTTPException:
                return self._unusable("Discord didn't answer when I looked the channel up")
        if not isinstance(channel, discord.TextChannel) or getattr(channel, "id", None) != ESO_OBSERVER_CHANNEL_ID:
            return self._unusable("it isn't a text channel")
        guild = channel.guild
        mod_log = self.bot.get_channel(MOD_LOG_CHANNEL_ID)
        if mod_log is not None and getattr(getattr(mod_log, "guild", None), "id", None) == getattr(guild, "id", None):
            return self._unusable("the channel is in the same server as the mod-log channel, so it is not the test server")
        me = getattr(guild, "me", None)
        if me is not None:  # (if the bot's own member isn't known yet, the send itself will show whether it is allowed)
            permissions = channel.permissions_for(me)
            if not (permissions.view_channel and permissions.send_messages):
                return self._unusable("I'm missing View Channel or Send Messages there")
        if self.problem:
            log.info("ESO observer: posting to the test channel again")
            self.problem = ""
        return channel

    async def _publish(self, messages: List[str], ping: bool = False) -> None:
        """Post these messages to the test channel, or just write them to the log if that isn't possible right now. With ping=True
        (used only for the ⚠️ warnings) the first message starts with an @mention of ESO_OBSERVER_PING_USER_ID, allowed to reach that
        member and nobody else, and the hourly limit below does not hold the warning back."""
        if not messages:
            return
        count = len(messages)
        who = ESO_OBSERVER_PING_USER_ID if ping and isinstance(ESO_OBSERVER_PING_USER_ID, int) and ESO_OBSERVER_PING_USER_ID > 0 else 0
        channel = await self._channel()
        now = time.monotonic()
        self.sent = [moment for moment in self.sent if now - moment < 3600]
        if channel is not None and not ping and len(self.sent) + len(messages) + (1 if self.held_back else 0) > _ESO_POSTS_PER_HOUR:
            self.held_back += len(messages)
            log.warning("ESO observer: %d message(s) held back, more than %d were posted in the last hour", len(messages), _ESO_POSTS_PER_HOUR)
            channel = None
        if channel is None:
            for text in messages:
                log.info("ESO observer (not posted):\n%s", text)
            return
        if self.held_back:
            messages = [f"_{self.held_back} earlier message(s) were held back to avoid flooding this channel._"] + messages
            self.held_back = 0
        for number, text in enumerate(messages):
            allowed = discord.AllowedMentions.none()
            if who and number == len(messages) - count:  # the warning itself (it comes after the "held back" note, if there is one)
                text = f"<@{who}> {text}"
                allowed = discord.AllowedMentions(everyone=False, roles=False, users=[discord.Object(id=who)], replied_user=False)
            try:
                await channel.send(text, allowed_mentions=allowed)
            except discord.HTTPException as error:
                log.warning("ESO observer: Discord refused a message (HTTP %s); the rest is only logged", getattr(error, "status", "?"))
                for rest in messages[number:]:
                    log.info("ESO observer (not posted):\n%s", rest)
                return
            self.sent.append(time.monotonic())

    # ----- one check --------------------------------------------------------

    async def _poll(self) -> None:
        loop = asyncio.get_running_loop()
        reply: Optional[_EsoReply] = None
        view: Optional[_EsoView] = None
        kind = ""
        try:
            reply, view = await asyncio.wait_for(loop.run_in_executor(None, _eso_check), _ESO_TOTAL_TIMEOUT)
        except asyncio.TimeoutError:
            kind = "timed out"
        except _EsoFetchError as error:
            kind, reply = error.kind, error.reply
        except Exception:
            log.exception("ESO observer: the page could not be read because of a fault in the observer")
            kind = "a fault in the observer (see the log)"
        if not kind and reply is not None and reply.status != 200:
            kind = f"HTTP {reply.status}"
        if kind or reply is None or view is None:
            await self._failed(kind or "no reading", reply)
        else:
            await self._good(reply, view)

    async def _failed(self, kind: str, reply: Optional[_EsoReply]) -> None:
        self.fails += 1
        self.failed_total += 1
        if self.fails == 1:
            self.failure_since = _utcnow()
            log.warning("ESO observer: the check failed (%s)", kind)
        elif self.fails % 30 == 0:
            log.warning("ESO observer: still failing after %d checks in a row (%s)", self.fails, kind)
        if self.fails >= _ESO_FAILS_BEFORE_NOTICE and not self.failure_noticed:
            self.failure_noticed = True
            sections = [("What came back", _eso_facts(reply, None) if reply is not None else f"nothing ({kind})")]
            if reply is not None and reply.body:
                sections.append(("Start of the reply", _eso_head(reply)))
            lead = f"⚠️ **ESO observer · the status page can't be read** · {_eso_when()}\n{self.fails} checks in a row failed. Latest: **{kind}**."
            await self._publish(_eso_messages(lead, sections), ping=True)

    async def _good(self, reply: _EsoReply, view: _EsoView) -> None:
        was_failing, noticed, since = self.fails, self.failure_noticed, self.failure_since
        self.fails, self.failure_noticed, self.failure_since = 0, False, None
        self.ok_total += 1
        now = _utcnow()
        if noticed:
            await self._publish([
                f"✅ **ESO observer · the status page can be read again** · {_eso_when(now)}\n"
                f"{was_failing} checks in a row had failed, starting {_eso_when(since)}."
            ])
        if not view.rows:  # the page came back fine but has no megaserver rows: it may have been redesigned or replaced
            if self.state != "no rows":
                self.state = "no rows"
                log.warning("ESO observer: the page was read but no megaserver rows were found")
                lead = f"⚠️ **ESO observer · the page has no megaserver rows** · {_eso_when(now)}\nIt came back fine, but I can't find the rows."
                await self._publish(_eso_capture(lead, reply, view, full=True, extra=(
                    ("Start of the page's text", view.head or "(no text)"), ("Start of the reply", _eso_head(reply)),
                )), ping=True)
            return
        previous, state_before = self.last_view, self.state
        self.state = "ok"
        self.last_view = view
        if previous is None:
            self.last_change = now
            log.info("ESO observer: first reading: %s", "; ".join(view.rows))
            await self._publish(_eso_capture(f"🔎 **ESO observer · first capture** · {_eso_when(now)}", reply, view, full=True))
        elif view.signature != previous.signature or state_before == "no rows":
            since_last = f" (before this, unchanged since {_eso_when(self.last_change)})" if self.last_change else ""
            self.last_change = now
            log.info("ESO observer: the page changed: %s", "; ".join(view.rows))
            what = "the megaserver rows are back" if state_before == "no rows" else "CHANGE"
            await self._publish(_eso_capture(
                f"🔄 **ESO observer · {what}** · {_eso_when(now)}{since_last}", reply, view, full=False, changes=_eso_diff(previous, view),
            ))
        else:
            log.debug("ESO observer: no change")

    async def _beat(self) -> None:
        if time.monotonic() - self.last_beat < _ESO_HEARTBEAT:
            return
        self.last_beat = time.monotonic()
        xbox = [row.replace("`", "'") for row in (self.last_view.rows if self.last_view else []) if "xbox" in row.lower()][:6]
        changed = _eso_when(self.last_change) if self.last_change else "none yet"
        await self._publish([
            f"💓 **ESO observer is still watching** · {_eso_when()}\n"
            f"Checks since the bot started: {self.ok_total} read, {self.failed_total} failed. Last change: {changed}.\n"
            f"Now: `{(' // '.join(xbox) if xbox else 'no Xbox rows seen yet')[:600]}`"
        ])

    # ----- the loop ---------------------------------------------------------

    async def _sleep(self, seconds: float) -> None:
        """Sleep in short slices so the observer notices at once that the bot is shutting down."""
        end = time.monotonic() + seconds
        while not self.bot.is_closed():
            left = end - time.monotonic()
            if left <= 0:
                return
            await asyncio.sleep(min(left, _ESO_SLEEP_SLICE))

    async def run(self) -> None:
        try:
            await self.bot.wait_until_ready()
            log.info("ESO observer started: checking every %s seconds", self.interval)
            await self._publish([
                f"👀 **ESO observer started** · {_eso_when()}\n"
                f"It checks <{_ESO_URL}> about every {int(self.interval)} seconds and posts what it sees here. "
                "It is observe-only: nothing is announced, and it pings its owner only when it posts a ⚠️ warning."
            ])
            while not self.bot.is_closed():
                try:
                    await self._poll()
                    await self._beat()
                except asyncio.CancelledError:
                    raise
                except Exception:
                    log.exception("ESO observer: unexpected error (it keeps going)")
                await self._sleep(self.interval)
        except asyncio.CancelledError:
            raise
        except Exception:
            log.exception("ESO observer stopped because of an unexpected error")
        finally:
            log.info("ESO observer stopped")


_eso_task: Optional[asyncio.Task] = None


@bot.listen("on_ready")
async def eso_observer_ready():
    """Start the observer once. on_ready fires again after every reconnect, so an observer that is already running is kept."""
    global _eso_task
    try:
        if not ESO_OBSERVER_ENABLED:
            log.info("ESO observer is switched off (the ESO_OBSERVER setting is off)")
        elif _eso_task is None or _eso_task.done():
            _eso_task = asyncio.create_task(_EsoObserver(bot, ESO_OBSERVER_INTERVAL).run(), name="eso-observer")
    except Exception:
        log.exception("The ESO observer could not be started")


# --------------------------------------------------------------------------
# /sos
#
# Replaces the old Carl-bot tag used to call for help in ESO Cyrodiil PvP. Open to every member on
# purpose -- no permission decorator -- because the whole point is that anyone under attack can raise
# the alarm. What stops it being spammed is a single cooldown shared by the WHOLE guild, with no
# exemption for any permission, role, or the server owner: SosManager (sos_state.json) is the only
# thing that decides whether a call goes out, and it is never asked who is calling.
#
# The cooldown only starts once the announcement has actually been posted (including the role ping);
# a failed send leaves it untouched. A per-guild asyncio.Lock (SosManager.lock) is held for the whole
# check-then-send-then-save sequence, so two /sos calls arriving at almost the same moment can't both
# get through.
# --------------------------------------------------------------------------


def _sos_announcement_embed(reason: str) -> discord.Embed:
    """The public announcement embed. Escaping the reason happens here, once, since this is the
    only place it's ever displayed."""
    safe_reason = discord.utils.escape_mentions(reason)
    embed = discord.Embed(
        title="You’re needed, soldier!!",
        description=(
            "Grand Warlord Dortene has received a rider bearing an urgent message from the battlefield:\n\n"
            f"> {safe_reason}\n\n"
            "Cyrodiil needs you! Rally to the cause and answer the call!\n\n"
            "*Anyone on the server can use `/sos` to put out a call for others to come online.*"
        ),
        colour=discord.Colour(0x1F3864),
    )
    embed.set_author(name="From High King Emeric")
    # The banner is the small icon next to the footer text, not a full-width image in the body.
    # Footers are plain text with no markdown, so the role-select pointer stays as plain text here
    # too -- it isn't repeated anywhere else in this embed.
    embed.set_footer(text="To stop receiving these notifications, head to #role-select", icon_url=SOS_BANNER_URL)
    return embed


def _sos_cooldown_embed(expires: datetime) -> discord.Embed:
    """The ephemeral embed shown when /sos is still on cooldown."""
    embed = discord.Embed(
        title="The Mists of Oblivion Still Linger",
        description=(
            "The call for aid has already been sent, soldier. Grand Warlord Dortene awaits the next "
            "dispatch, but the ravens have not yet returned. You may send another SOS when the "
            "cooldown has expired."
        ),
        colour=discord.Colour(0x6E6A7A),
    )
    embed.add_field(name="Cooldown", value=f"Another call may be sent {_fmt_relative(expires)}.", inline=False)
    return embed


@bot.tree.command(name="sos", description="Call for help in Cyrodiil. Shared 30-minute cooldown for the whole server.")
@app_commands.describe(reason="What's happening -- shown in the alert. Example: We are almost gated.")
@app_commands.guild_only()
async def sos(interaction: discord.Interaction, reason: app_commands.Range[str, 1, SOS_REASON_MAX]):
    guild = interaction.guild
    assert guild is not None  # guaranteed by guild_only()

    reason = reason.strip()
    if not reason:
        await interaction.response.send_message(
            "The reason can’t be empty, or just whitespace. Try again with a short description of "
            "what’s happening.",
            ephemeral=True,
        )
        return

    problem = _cannot_post_in(interaction.channel, guild.me)
    if problem:
        await interaction.response.send_message(
            f"I can’t post the SOS announcement in this channel ({problem}), so nothing was sent and "
            "the cooldown hasn’t started. Try again in a channel where I can send messages and embeds.",
            ephemeral=True,
        )
        return

    async with bot.sos.lock(guild.id):
        current = bot.sos.active_until(guild.id)
        if current is not None:
            await interaction.response.send_message(embed=_sos_cooldown_embed(current), ephemeral=True)
            return

        allowed = discord.AllowedMentions(everyone=False, users=False, roles=[discord.Object(id=SOS_ROLE_ID)])
        try:
            await interaction.response.send_message(
                content=f"<@&{SOS_ROLE_ID}>", embed=_sos_announcement_embed(reason), allowed_mentions=allowed,
            )
        except Exception:
            log.exception("/sos: could not post the announcement in guild %s (%s)", guild.name, guild.id)
            error_text = (
                "I couldn’t post the SOS announcement, so nothing was sent and the cooldown hasn’t "
                "started. Please try again."
            )
            try:
                if interaction.response.is_done():
                    await interaction.followup.send(error_text, ephemeral=True)
                else:
                    await interaction.response.send_message(error_text, ephemeral=True)
            except Exception:
                log.warning("/sos: could not tell the caller that sending failed", exc_info=True)
            return

        log.info(
            "/sos: announcement sent in guild %s (%s) by %s (%s): %r",
            guild.name, guild.id, interaction.user, interaction.user.id, reason,
        )
        await bot.sos.start(guild.id)


# --------------------------------------------------------------------------
# ESO Xbox server status: the monitor, /server and /server-sim
#
# What it does
#   Every couple of minutes the monitor reads https://esoserverstatus.net/ (the page Dwemer Automaton links to) and looks at two
#   rows only: XBOX EU and XBOX NA. PC and PlayStation are never announced. The site has no public API, so the status is read
#   from the page's own HTML: <span id="XBOX-EU">Online</span> and <span id="XBOX-NA">Offline</span>. The only words it trusts
#   are "Online" (up) and "Offline" (down); planned maintenance shows as "Offline" on that page, so it is announced as "down"
#   like any other outage. Any other word, a page that doesn't look right, a slow or failed request: all of those are
#   "unknown". Unknown means nothing is announced, nobody is pinged, and the last confirmed status is kept.
#
# When it announces
#   A change is believed only after two clear readings in a row agree on it, and is then announced once, per megaserver. The
#   first readings after start-up only set a baseline: nothing is announced. A status saved by the previous run is used again
#   only if it is fresh (less than about 20 minutes old). The new status is saved BEFORE the message is posted, so a restart
#   can never repeat an announcement. The price: an announcement that Discord refuses is logged, not retried.
#
# Where it posts
#   ONLY in the one channel for the current mode: the private test server (ESO_STATUS_TEST_GUILD_ID / _CHANNEL_ID), unless
#   the environment variable ESO_STATUS_LIVE is "on" AND the main-server IDs (ESO_STATUS_MAIN_GUILD_ID / _CHANNEL_ID) are filled
#   in. If an ID is missing, or doesn't check out (wrong server, not a text channel, missing permissions), nothing is posted
#   anywhere. Going live is a deliberate act: fill in the two main-server IDs and set ESO_STATUS_LIVE to on.
#
# Pings
#   Only "Online" straight after "Offline" pings, and only the one role of that megaserver (EU_PING_ROLE_ID or
#   NA_PING_ROLE_ID), written in the message text with Discord's allowed-mentions limited to that role. Never @everyone or
#   @here, never for "down", at start-up, after a failure or for an unknown status. A role that is 0, doesn't exist in the
#   server, can't be mentioned or is shared by both regions gives the ordinary announcement without a ping. In the test server
#   nobody is pinged unless ESO_STATUS_TEST_PINGS is "on".
#
# The category (ESO_STATUS_CATEGORY_ID, only while the bot is live in the main server)
#   Its name is always "Xbox EU 🟢┊🟢 Xbox NA": one circle for each megaserver, 🟢 for up and 🔴 for down. Ninety seconds after a status change is
#   confirmed (so after the announcement, not with it, and so that EU and NA changing together is one rename, not two) the name is set to
#   exactly that layout. A name that is already exactly right is left alone. If somebody renames the category by hand, the bot notices within
#   seconds (it compares the name it last gave the category with its own copy, which costs nothing) and puts the standard name straight
#   back, at most six times an hour so that nobody can use it to flood the audit log; a status change still renames it. Nothing happens
#   until both statuses are known. The bot needs the Manage Channels permission for that category. Discord allows two renames of one
#   channel in ten minutes.
#
# /server (EU or NA) shows the status, taken fresh from the page (at most once a minute) and never announces or pings anything.
# /server-sim (test server only, Manage Server permission) posts a clearly labelled simulation in the test channel. It cannot
# touch the monitor's saved status and cannot ping anyone unless test pings are switched on AND you pick the "real test ping" event.
# --------------------------------------------------------------------------

_ESOM_URL = "https://esoserverstatus.net/"
_ESOM_LINK = "https://esoserverstatus.net/"  # what the embeds link to (the page itself)
_ESOM_HOSTS = ("esoserverstatus.net", "www.esoserverstatus.net")  # a redirect may only lead to one of these...
_ESOM_SCHEMES = ("https",)  # ...over https
_ESOM_REGIONS = ("EU", "NA")  # the two megaservers, in this order everywhere
_ESOM_IDS = {"XBOX-EU": "EU", "XBOX-NA": "NA"}  # the id="..." of each status on the page
_ESOM_UP_WORDS = ("online",)  # the only words that count as up...
_ESOM_DOWN_WORDS = ("offline",)  # ...and as down; anything else is "unknown"
_ESOM_TIMEOUT = 10  # seconds the site gets for each step of a request
_ESOM_TOTAL_TIMEOUT = 25  # seconds for a whole check, reading the page included
_ESOM_MAX_BYTES = 400_000  # the real page is about 25,000 bytes; a bigger one is not accepted
_ESOM_MAX_TOKENS = 20_000  # pieces of markup and text looked at; the real page has fewer than a thousand
_ESOM_CONFIRM = 2  # clear readings in a row that must agree before a change is believed
_ESOM_RESTART_GRACE = 20 * 60  # seconds; a status saved longer ago than this is not trusted after a restart
_ESOM_TOUCH_EVERY = 300  # seconds between "still alive" refreshes of the saved file when nothing has changed
_ESOM_CACHE_SECONDS = 60  # /server reuses a reading this young instead of asking the site again
_ESOM_STALE_AFTER = 300  # seconds; an older reading is not shown as the current status
_ESOM_MAX_PER_HOUR = 10  # the most announcements for one megaserver in an hour, however often it seems to change
_ESOM_BACKOFF_CAP = 600  # seconds; the longest wait between checks while the site keeps failing
_ESOM_SEND_TIMEOUT = 30  # seconds Discord gets to accept a message
_ESOM_SLEEP_SLICE = 5  # seconds; the monitor sleeps in slices this long so it notices at once that the bot is closing
_ESOM_RED, _ESOM_GREEN, _ESOM_GREY = 0xFF0000, 0x00FF00, 0x95A5A6  # Dwemer's "down" embed is exactly this red
_ESOM_CATEGORY_DELAY = 90  # seconds a combination of statuses must have stood before the category is renamed (the announcement goes out at once)
_ESOM_CATEGORY_TICK = 5  # seconds between looks at the two statuses and at the category's name
_ESOM_CATEGORY_TIMEOUT = 30  # seconds Discord gets to accept a rename (it allows only two renames of one channel in ten minutes)
_ESOM_CATEGORY_RETRY = 600  # seconds to wait before trying again after a rename could not be done
_ESOM_CATEGORY_QUIET = 30  # seconds after the bot's own rename before the name is checked for a hand-made change (the bot's copy of the name lags a moment)
_ESOM_CATEGORY_REPAIRS_PER_HOUR = 6  # the most times the name is put back after a hand-made change in an hour (a status change is never held back)


def _esom_flag(name: str, default: bool) -> bool:
    """An on/off setting from the environment. Not set: the default. Set to anything that isn't clearly on or off: off, which
    is the safe side for every switch here, and a warning says so."""
    value = os.environ.get(name)
    if value is None or not value.strip():
        return default
    word = value.strip().lower()
    if word in ("on", "1", "true", "yes"):
        return True
    if word in ("off", "0", "false", "no"):
        return False
    log.warning("%s is set to something other than on or off, so it is treated as off.", name)
    return False


_ESOM_ENABLED = _esom_flag("ESO_STATUS_MONITOR", True)  # off switches the background monitor off (/server still works)
_ESOM_LIVE = _esom_flag("ESO_STATUS_LIVE", False)  # on: announce in the main server instead of the test server
_ESOM_TEST_PINGS = _esom_flag("ESO_STATUS_TEST_PINGS", False)  # on: allow role pings in the test server
try:
    _ESOM_INTERVAL = min(3600, max(60, int(os.environ.get("ESO_STATUS_INTERVAL_SECONDS", "120"))))
except ValueError:
    _ESOM_INTERVAL = 120
# Where the last known status is kept: ESO_STATUS_STATE_PATH if set, else /data when that folder exists, else next to this script.
_ESOM_STATE_FILE = Path(
    os.environ.get("ESO_STATUS_STATE_PATH")
    or (Path("/data/eso_status_state.json") if Path("/data").is_dir() else Path(__file__).parent / "eso_status_state.json")
)


def _esom_id(value: Any) -> int:
    """A usable Discord ID from one of the settings above, or 0 if it isn't one (0 itself, a negative number, text...)."""
    return value if isinstance(value, int) and not isinstance(value, bool) and value > 0 else 0


def _esom_target() -> Tuple[str, int, int]:
    """(mode, server ID, channel ID) of the one place announcements may go. "live" only when ESO_STATUS_LIVE is on."""
    if _ESOM_LIVE:
        return "live", _esom_id(ESO_STATUS_MAIN_GUILD_ID), _esom_id(ESO_STATUS_MAIN_CHANNEL_ID)
    return "test", _esom_id(ESO_STATUS_TEST_GUILD_ID), _esom_id(ESO_STATUS_TEST_CHANNEL_ID)


def _esom_command_guilds() -> Tuple[int, ...]:
    """The servers where /server exists: the test server, plus the main server once ESO_STATUS_LIVE is on."""
    ids = [_esom_id(ESO_STATUS_TEST_GUILD_ID)]
    if _ESOM_LIVE:
        ids.append(_esom_id(ESO_STATUS_MAIN_GUILD_ID))
    return tuple(dict.fromkeys(server for server in ids if server))


def _esom_config_problem() -> str:
    """Why the monitor can't run with the current settings, or "" if they are complete."""
    mode, guild_id, channel_id = _esom_target()
    if guild_id and channel_id:
        return ""
    if mode == "live":
        return "ESO_STATUS_LIVE is on, but ESO_STATUS_MAIN_GUILD_ID and ESO_STATUS_MAIN_CHANNEL_ID are not both filled in"
    return "ESO_STATUS_TEST_GUILD_ID and ESO_STATUS_TEST_CHANNEL_ID are not both filled in"


def _esom_now() -> datetime:
    return _utcnow()


def _esom_mono() -> float:
    return time.monotonic()


# ----- reading the page ----------------------------------------------------------------------------------------

class _EsomError(Exception):
    """A check that produced no trustworthy reading. `kind` is a short plain description; it never holds an address or page text."""

    def __init__(self, kind: str) -> None:
        super().__init__(kind)
        self.kind = kind


class _EsomReply:
    """What came back from one request."""

    def __init__(self, status: int, body: bytes, content_type: str, encoding: str, charset: str, cut: bool) -> None:
        self.status, self.body, self.content_type = status, body, content_type
        self.encoding, self.charset, self.cut = encoding, charset, cut

    @property
    def text(self) -> str:
        try:
            return self.body.decode(self.charset, errors="replace")
        except LookupError:  # a character set Python doesn't know
            return self.body.decode("utf-8", errors="replace")


class _EsomReading:
    """One successful reading of the page: when it was taken and, for each megaserver, its status ("up", "down" or "unknown")
    and the word the page showed."""

    def __init__(self, at: datetime, found: Dict[str, Tuple[str, str]]) -> None:
        self.at = at
        self.status = {region: found[region][0] for region in _ESOM_REGIONS}
        self.word = {region: found[region][1] for region in _ESOM_REGIONS}


class _EsomRedirects(urllib.request.HTTPRedirectHandler):
    max_redirections = 3

    def redirect_request(self, req: Any, fp: Any, code: int, msg: str, headers: Any, newurl: str) -> Any:
        target = urllib.parse.urlsplit(newurl)
        if target.scheme not in _ESOM_SCHEMES or (target.hostname or "").lower() not in _ESOM_HOSTS:
            return None  # anywhere else counts as a failed check, not something to follow
        return super().redirect_request(req, fp, code, msg, headers, newurl)


def _esom_error_kind(error: BaseException) -> str:
    """A short plain description of why a request failed. Only the kind of error is used, never its message."""
    reason = getattr(error, "reason", None)  # a URLError carries the real cause here
    if not isinstance(reason, BaseException):
        if isinstance(error, urllib.error.URLError):
            return "connection problem"
        reason = error
    name = type(reason).__name__
    if isinstance(reason, TimeoutError) or name == "timeout":
        return "timed out"
    if "SSL" in name or "Certificate" in name:
        return "TLS/certificate problem"
    if name == "gaierror":
        return "the name could not be looked up (DNS)"
    if isinstance(reason, ConnectionRefusedError):
        return "connection refused"
    if isinstance(reason, (ConnectionResetError, ConnectionAbortedError, BrokenPipeError)) or name in (
        "IncompleteRead", "RemoteDisconnected", "BadStatusLine",
    ):
        return "connection dropped"
    if isinstance(reason, OSError):
        return "could not connect"
    return "connection problem"


def _esom_read(response: Any, status: int, started: float) -> _EsomReply:
    """Read the body (up to the size limit and the overall time limit) and note the few headers that matter."""
    deadline = started + _ESOM_TOTAL_TIMEOUT - 3
    chunks: List[bytes] = []
    size, cut = 0, False
    take = getattr(response, "read1", response.read)  # read1 returns what has arrived, so a site that trickles can't hold this up
    while True:
        if time.monotonic() > deadline:
            raise _EsomError("timed out")
        chunk = take(65536)
        if not chunk:
            break
        chunks.append(chunk)
        size += len(chunk)
        if size > _ESOM_MAX_BYTES:
            cut = True
            break
    message = response.headers
    promised = message.get("content-length")
    if not cut and promised is not None and promised.strip().isdigit() and size < int(promised):
        raise _EsomError("connection dropped")  # the site hung up before the whole page arrived
    return _EsomReply(
        status, b"".join(chunks)[:_ESOM_MAX_BYTES], message.get("content-type") or "",
        (message.get("content-encoding") or "identity").strip().lower(), message.get_content_charset() or "utf-8", cut,
    )


def _esom_request() -> _EsomReply:
    """One GET of the status page. It blocks, so it runs in a worker thread."""
    started = time.monotonic()
    request = urllib.request.Request(_ESOM_URL, headers={
        "User-Agent": f"PossBot/1.0 (Discord bot; read-only ESO Xbox status check; about one request every {_ESOM_INTERVAL} seconds)",
        "Accept": "text/html,application/xhtml+xml;q=0.9,*/*;q=0.5",
        "Accept-Encoding": "identity",
    })
    try:
        with urllib.request.build_opener(_EsomRedirects).open(request, timeout=_ESOM_TIMEOUT) as response:
            return _esom_read(response, response.status, started)
    except urllib.error.HTTPError as error:  # 4xx, 5xx and a refused redirect: an answer, but not a reading
        with error:
            raise _EsomError(f"HTTP {error.code}") from None
    except _EsomError:
        raise
    except Exception as error:
        raise _EsomError(_esom_error_kind(error)) from None


def _esom_strip_comments(page: str) -> str:
    """The page without its <!-- comments -->, so markup that is commented out can't be mistaken for a status. One pass."""
    parts: List[str] = []
    pos = 0
    while True:
        start = page.find("<!--", pos)
        if start < 0:
            parts.append(page[pos:])
            break
        parts.append(page[pos:start])
        end = page.find("-->", start + 4)
        if end < 0:  # never closed: browsers treat the rest of the page as the comment, and so does this
            break
        pos = end + 3
    return "".join(parts)


_ESOM_TAG = re.compile(r"<(/?)([A-Za-z][A-Za-z0-9]*)([^<>]*)>")
_ESOM_ID_ATTR = re.compile(r"""(?is)(?:^|\s)id\s*=\s*(?:"([^"]*)"|'([^']*)'|([^\s"'<>=`]+))""")


def _esom_tokens(page: str) -> List[Tuple[str, ...]]:
    """The page as a flat list of pieces: ("<", tag, attributes) for an opening tag, (">", tag) for a closing one and
    ("t", text) for a run of text. What is inside <script> and <style> is skipped. One pass with no nested searching, so a
    damaged or hostile page can't make it slow."""
    page = _esom_strip_comments(page)
    lowered = page.replace("\u0130", "i").lower()  # keeps every character where it was (the dotted capital I is the one that wouldn't)
    tokens: List[Tuple[str, ...]] = []
    pos, size = 0, len(page)

    def add_text(raw: str) -> None:
        text = " ".join(html.unescape(raw).split())
        if text:
            tokens.append(("t", text))

    while pos < size:
        if len(tokens) >= _ESOM_MAX_TOKENS:
            raise _EsomError("the page has far more markup than expected")
        tag = _ESOM_TAG.search(page, pos)
        if tag is None:
            add_text(page[pos:])
            break
        if tag.start() > pos:
            add_text(page[pos:tag.start()])
        pos = tag.end()
        name = tag.group(2).lower()
        if tag.group(1):
            tokens.append((">", name))
            continue
        tokens.append(("<", name, tag.group(3)))
        if name in ("script", "style") and not tag.group(3).rstrip().endswith("/"):
            end = lowered.find("</" + name, pos)
            pos = size if end < 0 else end  # the closing tag itself is read normally next time round
    return tokens


def _esom_label_ok(label: str, region: str) -> bool:
    """True if the row's visible label says Xbox and this region, e.g. "XBOX EU Megaserver"."""
    words = re.findall(r"[a-z0-9]+", label.lower())
    other = "na" if region == "EU" else "eu"
    return "xbox" in words and region.lower() in words and other not in words


def _esom_parse(page: str) -> Dict[str, Tuple[str, str]]:
    """The status of XBOX EU and XBOX NA from the page's HTML: {"EU": ("up", "Online"), "NA": ("down", "Offline")}.

    Each must be found exactly once, as <span id="XBOX-EU">...</span> outside any script, sitting in a row whose visible label
    says the same Xbox region, with nothing but text inside. Anything else raises _EsomError, because a page that doesn't look
    like the one this was checked against is not to be trusted. A word other than Online/Offline is "unknown"."""
    tokens = _esom_tokens(page)
    found: Dict[str, List[Tuple[str, str]]] = {region: [] for region in _ESOM_REGIONS}
    for i, token in enumerate(tokens):
        if token[0] != "<" or token[1] != "span":
            continue
        match = _ESOM_ID_ATTR.search(token[2])
        ident = next((group for group in match.groups() if group is not None), "") if match else ""
        region = _ESOM_IDS.get(ident.strip().upper())
        if region is None:
            continue
        inside = tokens[i + 1] if i + 1 < len(tokens) else ("",)
        after = tokens[i + 2] if i + 2 < len(tokens) else ("",)
        if inside[0] == "t" and after[0] == ">" and after[1] == "span":
            word = inside[1]
        elif inside[0] == ">" and inside[1] == "span":  # an empty span
            word = ""
        else:
            raise _EsomError(f"XBOX-{region} has unexpected markup around its status")
        label = ""
        for j in range(i - 1, -1, -1):  # the nearest text before it, without leaving its row
            if tokens[j][0] == "<" and tokens[j][1] == "tr":
                break
            if tokens[j][0] == "t":
                label = tokens[j][1]
                break
        found[region].append((label, word))
    result: Dict[str, Tuple[str, str]] = {}
    for region in _ESOM_REGIONS:
        entries = found[region]
        if len(entries) != 1:
            raise _EsomError(f"XBOX-{region} was {'not found' if not entries else 'found more than once'} on the page")
        label, word = entries[0]
        if not _esom_label_ok(label, region):
            raise _EsomError(f"the label next to XBOX-{region} does not say Xbox {region}")
        lowered = word.lower()
        status = "up" if lowered in _ESOM_UP_WORDS else "down" if lowered in _ESOM_DOWN_WORDS else "unknown"
        result[region] = (status, word[:40])
    return result


def _esom_check() -> Dict[str, Tuple[str, str]]:
    """One whole check, run in a worker thread: fetch the page, make sure it is a normal answer, and read the two statuses."""
    reply = _esom_request()
    if reply.status != 200:
        raise _EsomError(f"HTTP {reply.status}")
    if reply.cut:
        raise _EsomError("the page is much bigger than expected")
    if "html" not in reply.content_type.lower():
        raise _EsomError("the reply was not a web page")
    if reply.encoding not in ("", "identity"):
        raise _EsomError("the page came back compressed, which was not asked for")
    return _esom_parse(reply.text)


# ----- the latest reading, shared by the monitor and /server -------------------------------------------------------

_ESOM_LATEST: Optional[_EsomReading] = None  # the newest successful reading, whoever took it
_esom_locks: Dict[str, asyncio.Lock] = {}


def _esom_lock(name: str) -> asyncio.Lock:
    """One lock per purpose, made on first use so that it belongs to the event loop that is running."""
    lock = _esom_locks.get(name)
    if lock is None:
        lock = _esom_locks[name] = asyncio.Lock()
    return lock


async def _esom_fetch_reading(max_age: Optional[float]) -> _EsomReading:
    """Take a reading from the page (in a worker thread, so the bot never waits for it). With max_age, a reading that young is
    returned instead of asking the site again. Only one request is ever in flight; others wait and share its result.
    Raises _EsomError if no trustworthy reading could be taken."""
    global _ESOM_LATEST
    async with _esom_lock("fetch"):
        latest = _ESOM_LATEST
        if max_age is not None and latest is not None and 0 <= (_esom_now() - latest.at).total_seconds() <= max_age:
            return latest
        try:
            found = await asyncio.wait_for(asyncio.get_running_loop().run_in_executor(None, _esom_check), _ESOM_TOTAL_TIMEOUT)
            reading = _EsomReading(_esom_now(), found)  # (also inside the guard: an answer of the wrong shape is a failed check)
        except asyncio.TimeoutError:
            raise _EsomError("timed out") from None
        except _EsomError:
            raise
        except Exception:
            log.exception("Xbox status: the page could not be read because of a fault in the status check")
            raise _EsomError("a fault in the status check (see the log)") from None
        _ESOM_LATEST = reading
        return reading


# ----- what each megaserver is believed to be ------------------------------------------------------------------------

class _EsomServer:
    """What the monitor believes about one megaserver. `state` is the last CONFIRMED status ("up" or "down"), None until a
    baseline is set. A different status becomes the new state only after _ESOM_CONFIRM clear readings in a row agree on it."""

    def __init__(self, region: str) -> None:
        self.region = region
        self.state: Optional[str] = None
        self.since: Optional[datetime] = None  # when `state` was confirmed
        self.checked_at: Optional[datetime] = None  # when the page was last read successfully
        self.candidate: Optional[str] = None  # a different status being counted
        self.count = 0

    def miss(self) -> None:
        """A check that gave no reading. It breaks any run of agreeing readings: they must follow one another."""
        self.candidate, self.count = None, 0

    def feed(self, status: str, now: datetime) -> Optional[str]:
        """Take one reading. Returns None (nothing to say), "baseline" (the first confirmed status: nothing to announce) or
        "up" / "down" (a confirmed change to announce)."""
        self.checked_at = now
        if status not in ("up", "down"):  # unknown or ambiguous: neither online nor offline
            self.candidate, self.count = None, 0
            return None
        if status == self.state:
            self.candidate, self.count = None, 0
            return None
        if status == self.candidate:
            self.count += 1
        else:
            self.candidate, self.count = status, 1
        if self.count < _ESOM_CONFIRM:
            return None
        previous = self.state
        self.state, self.since = status, now
        self.candidate, self.count = None, 0
        return "baseline" if previous is None else status


class _EsomStore:
    """The monitor's one small state file. Knows nothing about Discord. It is saved atomically (a temporary file, then a swap),
    and a file that can't be read is moved aside, never overwritten."""

    def __init__(self, path: Path) -> None:
        self._path = path
        self._lock: Optional[asyncio.Lock] = None  # created on first use, inside the running event loop
        self._unsafe = False  # True if an unreadable file could not be moved aside

    def _set_aside(self, label: str) -> Optional[Path]:
        target = self._path.with_name(f"{self._path.name}.{label}-{_utcnow().strftime('%Y%m%dT%H%M%SZ')}")
        try:
            os.replace(self._path, target)
            return target
        except OSError:
            log.exception("Xbox status monitor: could not set aside %s", self._path)
            return None

    def _unusable(self, error: BaseException) -> Dict[str, Dict[str, Any]]:
        log.error("Xbox status monitor: its saved-status file is unreadable (%s).", type(error).__name__)
        saved = self._set_aside("corrupt")
        if saved is None:
            self._unsafe = True  # refuse to write, so the damaged file can't be overwritten
            log.error("Xbox status monitor: the unreadable file could not be moved aside, so nothing will be saved until it is fixed.")
        else:
            log.error("Xbox status monitor: the unreadable file was kept as %s and the monitor starts with no saved status.", saved.name)
        return {}

    def load(self) -> Dict[str, Dict[str, Any]]:
        """The saved status of each megaserver, {"EU": {"state": "up", "since": datetime, "checked_at": datetime}, ...}. Empty if
        there is no usable file."""
        try:
            text = self._path.read_text(encoding="utf-8")
        except FileNotFoundError:
            return {}  # first run
        except OSError as error:
            return self._unusable(error)
        try:
            servers = json.loads(text)["servers"]
            if not isinstance(servers, dict):
                raise ValueError("'servers' is not an object")
        except (ValueError, KeyError, TypeError) as error:
            return self._unusable(error)
        saved: Dict[str, Dict[str, Any]] = {}
        for region in _ESOM_REGIONS:
            if region not in servers:
                continue
            try:
                entry = servers[region]
                if entry["state"] not in ("up", "down"):
                    raise ValueError("not up or down")
                saved[region] = {
                    "state": entry["state"], "since": _parse_time(entry["since"]), "checked_at": _parse_time(entry["checked_at"]),
                }
            except (ValueError, KeyError, TypeError, AttributeError):
                log.warning("Xbox status monitor: the saved status for XBOX %s is not valid and is ignored.", region)
        return saved

    def _write(self, text: str) -> None:
        self._path.parent.mkdir(parents=True, exist_ok=True)
        temp = self._path.with_name(self._path.name + ".tmp")
        try:
            with open(temp, "w", encoding="utf-8") as handle:
                handle.write(text)
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temp, self._path)  # all-or-nothing swap
        except OSError:
            with contextlib.suppress(OSError):
                os.remove(temp)
            raise

    async def save(self, snapshot: Dict[str, Any]) -> None:
        """Write the snapshot atomically. Raises OSError if the file can't be written."""
        if self._lock is None:
            self._lock = asyncio.Lock()
        async with self._lock:
            if self._unsafe:
                raise OSError("the saved-status file is unreadable and was not moved aside; refusing to overwrite it")
            await asyncio.get_running_loop().run_in_executor(None, self._write, json.dumps(snapshot, indent=2, sort_keys=True))


# ----- the messages --------------------------------------------------------------------------------------------------

def _esom_footer(region: str) -> str:
    return f"Poss Bot watching [server-xbox-{region}]"


def _esom_change_embed(region: str, direction: str, simulated: bool = False) -> Any:
    """Dwemer Automaton's "Server status update" embed: the title is the link to ESO Server Status, then one line with the
    emoji and "The XBOX EU server is now down." / "...now up.", and a footer naming the server."""
    up = direction == "up"
    embed = discord.Embed(
        title="Server status update" + (" (simulation)" if simulated else ""),
        url=_ESOM_LINK,
        description=f"{'✅' if up else '❌'} The XBOX {region} server is now {'up' if up else 'down'}.",
        colour=discord.Colour(_ESOM_GREEN if up else _ESOM_RED),
    )
    embed.set_footer(text=_esom_footer(region) + (" · SIMULATION, not a real status change" if simulated else ""))
    return embed


def _esom_message(region: str, direction: str, role: Optional[Any] = None, simulated: bool = False, note: str = "") -> Tuple[Optional[str], Any, Any]:
    """(text, embed, allowed mentions) for one announcement. The text is empty (None) unless a role is to be pinged, so an
    ordinary announcement is just the embed, as Dwemer's are. A ping is the role's mention in the text, and the allowed
    mentions allow that one role and nothing else: no @everyone, no @here, no members, no other role."""
    embed = _esom_change_embed(region, direction, simulated)
    if role is not None:
        text: Optional[str] = f"<@&{role.id}>"  # just the mention: the embed already says it
        allowed = discord.AllowedMentions(everyone=False, users=False, roles=[discord.Object(id=role.id)], replied_user=False)
    else:
        text = None
        allowed = discord.AllowedMentions.none()
    if simulated:
        text = "🧪 **SIMULATION**: a test, not a real status change." + (f" {note}" if note else "") + (f"\n{text}" if text else "")
    return text, embed, allowed


def _esom_status_embed(region: str, reading: Optional[_EsomReading], fresh: bool, now: datetime) -> Any:
    """The /server answer. A reading older than _ESOM_STALE_AFTER is never shown as the status, only as when it was last checked."""
    label = f"XBOX {region}"
    usable = reading is not None and 0 <= (now - reading.at).total_seconds() <= _ESOM_STALE_AFTER
    colour = _ESOM_GREY
    lines: List[str] = []
    if usable and reading is not None:
        status, word = reading.status[region], reading.word[region]
        if status == "up":
            lines.append(f"✅ The {label} server is **up**.")
            colour = _ESOM_GREEN
        elif status == "down":
            lines.append(f"❌ The {label} server is **down**.")
            colour = _ESOM_RED
        else:
            shown = discord.utils.escape_markdown(discord.utils.escape_mentions(word or "nothing"))
            lines.append(f"❓ I can’t tell whether the {label} server is up or down: ESO Server Status shows “{shown}”.")
        lines.append(f"Last checked {_fmt_relative(reading.at)} ({reading.at:%H:%M:%S} UTC).")
        if not fresh:
            lines.append("I couldn’t check again just now, so this is from my last successful check.")
    else:
        lines.append(f"❓ I couldn’t check the {label} server just now, so I can’t say whether it is up or down.")
        if reading is not None:
            lines.append(f"My last successful check was {_fmt_relative(reading.at)} ({reading.at:%H:%M:%S} UTC), which is too long ago to rely on.")
    lines.append(f"Source: [ESO Server Status]({_ESOM_LINK})")
    embed = discord.Embed(title="Server status", url=_ESOM_LINK, description="\n".join(lines), colour=discord.Colour(colour))
    embed.set_footer(text=_esom_footer(region))
    return embed


# ----- where announcements go, and who may be pinged ---------------------------------------------------------------------

async def _esom_destination(client: Any, mode: str) -> Tuple[Optional[Any], str]:
    """The channel announcements for this mode go to, or (None, why it can't be used right now). This is the only way the
    monitor and the simulation ever find a channel to post in: the configured server, the configured channel, and nothing else."""
    if mode == "live":
        guild_id, channel_id = _esom_id(ESO_STATUS_MAIN_GUILD_ID), _esom_id(ESO_STATUS_MAIN_CHANNEL_ID)
        names = "ESO_STATUS_MAIN_GUILD_ID and ESO_STATUS_MAIN_CHANNEL_ID"
    else:
        mode = "test"
        guild_id, channel_id = _esom_id(ESO_STATUS_TEST_GUILD_ID), _esom_id(ESO_STATUS_TEST_CHANNEL_ID)
        names = "ESO_STATUS_TEST_GUILD_ID and ESO_STATUS_TEST_CHANNEL_ID"
    if not guild_id or not channel_id:
        return None, f"{names} are not both filled in"
    guild = client.get_guild(guild_id)
    if guild is None:
        return None, "the bot is not in the server with that ID"
    channel = guild.get_channel(channel_id)
    if channel is None:
        try:
            channel = await client.fetch_channel(channel_id)
        except discord.NotFound:
            return None, "that channel does not exist"
        except discord.Forbidden:
            return None, "the bot cannot see that channel"
        except discord.HTTPException:
            return None, "Discord did not answer when the channel was looked up"
    if not isinstance(channel, discord.TextChannel) or getattr(channel, "id", None) != channel_id:
        return None, "that is not a text channel"
    if getattr(getattr(channel, "guild", None), "id", None) != guild_id:
        return None, "that channel is in a different server from the one configured"
    mod_log = client.get_channel(MOD_LOG_CHANNEL_ID)  # the mod-log channel says which server is the main one
    main_id = getattr(getattr(mod_log, "guild", None), "id", None)
    if main_id is not None:
        if mode == "test" and main_id == guild_id:
            return None, "that server is the main server (the mod-log channel is in it), so it is not the test server"
        if mode == "live" and main_id != guild_id:
            return None, "that server is not the main server (the mod-log channel is in a different one)"
    me = getattr(guild, "me", None)
    if me is not None:  # (if the bot's own member isn't known yet, the send itself will show whether it is allowed)
        permissions = channel.permissions_for(me)
        missing = [name.replace("_", " ") for name in ("view_channel", "send_messages", "embed_links") if not getattr(permissions, name, False)]
        if missing:
            return None, "the bot is missing these permissions in that channel: " + ", ".join(missing)
    return channel, ""


def _esom_pick_role(channel: Any, region: str, live: bool, gate: bool = True) -> Tuple[Optional[Any], str, bool]:
    """The one role that may be pinged for a restoration of this megaserver, or (None, why not, whether that is a problem to
    warn about). `live` is whether the channel is in the main server; in the test server nobody is pinged unless
    ESO_STATUS_TEST_PINGS is on (gate=False looks at the role only, which is how the simulation checks a role without pinging it)."""
    role_id = _esom_id(NA_PING_ROLE_ID if region == "NA" else EU_PING_ROLE_ID)
    if not role_id:
        return None, "no ping role is set for this megaserver", False
    if role_id == _esom_id(EU_PING_ROLE_ID if region == "NA" else NA_PING_ROLE_ID):
        return None, "the NA and EU ping roles are the same role, so neither is used", True
    if gate and not live and not _ESOM_TEST_PINGS:
        return None, "pings are switched off in the test server (ESO_STATUS_TEST_PINGS)", False
    guild = channel.guild
    role = guild.get_role(role_id)
    if role is None:
        return None, f"role {role_id} does not exist in this server", True
    if role.id == guild.id:  # the @everyone role has the same ID as its server
        return None, "that is the @everyone role", True
    if not getattr(role, "mentionable", False):
        me = getattr(guild, "me", None)
        if me is None or not getattr(channel.permissions_for(me), "mention_everyone", False):
            return None, f"role {role_id} is not mentionable and the bot does not have the Mention Everyone permission", True
    return role, "", False


# ----- the monitor ---------------------------------------------------------------------------------------------------

class _EsomMonitor:
    """Checks the page every `interval` seconds, keeps a confirmed status for each megaserver, saves it, and announces confirmed
    changes. It never reacts to a failed or unclear reading except by logging it."""

    def __init__(self, client: Any, interval: float, path: Path) -> None:
        self.bot = client
        self.interval = interval
        self.store = _EsomStore(path)
        self.servers = {region: _EsomServer(region) for region in _ESOM_REGIONS}
        self.fails = 0  # checks in a row that gave no reading
        self.polling = False
        self.saved_at: Optional[float] = None
        self.sent: Dict[str, List[float]] = {region: [] for region in _ESOM_REGIONS}  # when each recent announcement was posted
        self.noted: Set[str] = set()  # things already logged, so each is logged once
        self.odd: Dict[str, Optional[str]] = {region: None for region in _ESOM_REGIONS}  # the unclear word last logged for each megaserver

    def _note(self, key: str, level: int, message: str, *args: Any) -> None:
        if key not in self.noted:
            self.noted.add(key)
            log.log(level, message, *args)

    # ----- start-up ---------------------------------------------------------

    def restore(self) -> None:
        """Pick up the status the previous run saved, but only a fresh one: a status that old can't be told apart from a change
        that happened while the bot was off, so after a long absence a new baseline is taken silently."""
        now = _esom_now()
        grace = max(_ESOM_RESTART_GRACE, 5 * self.interval)
        for region, entry in self.store.load().items():
            age = (now - entry["checked_at"]).total_seconds()
            if -300 <= age <= grace:
                server = self.servers[region]
                server.state, server.since, server.checked_at = entry["state"], entry["since"], entry["checked_at"]
                log.info("Xbox status monitor: XBOX %s was %s when last seen %d minute(s) ago; carrying on from that.", region, entry["state"], max(0, int(age // 60)))
            else:
                log.info("Xbox status monitor: the saved status for XBOX %s can't be trusted (too old, or dated in the future); a fresh baseline will be taken without announcing anything.", region)

    async def check_destination(self) -> None:
        """Say in the log, once at start-up, where announcements will go and what each ping role is going to do."""
        mode, _, _ = _esom_target()
        channel, problem = await _esom_destination(self.bot, mode)
        if channel is None:
            log.warning("Xbox status monitor: nothing can be announced right now: %s.", problem)
            return
        log.info("Xbox status monitor: announcements go to #%s in “%s” (%s mode).", getattr(channel, "name", "?"), getattr(channel.guild, "name", "?"), mode)
        for region in _ESOM_REGIONS:
            role, why, serious = _esom_pick_role(channel, region, live=(mode == "live"))
            if role is not None:
                log.info("Xbox status monitor: XBOX %s restorations will ping the role “%s”.", region, getattr(role, "name", role.id))
            else:
                log.log(logging.WARNING if serious else logging.INFO, "Xbox status monitor: XBOX %s restorations will not ping anyone: %s.", region, why)

    # ----- saving -----------------------------------------------------------

    def _snapshot(self, now: datetime) -> Dict[str, Any]:
        servers = {}
        for region, server in self.servers.items():
            if server.state is not None and server.since is not None:
                servers[region] = {"state": server.state, "since": _iso(server.since), "checked_at": _iso(server.checked_at or now)}
        return {"version": 1, "saved_at": _iso(now), "servers": servers}

    async def _save(self, now: datetime) -> None:
        snapshot = self._snapshot(now)
        if not snapshot["servers"]:
            return  # nothing is confirmed yet, so there is nothing worth keeping
        self.saved_at = _esom_mono()
        try:
            await self.store.save(snapshot)
        except OSError as error:
            self._note("save", logging.ERROR, "Xbox status monitor: could not save its status (%s). It keeps working, but a restart will start with a fresh baseline.", type(error).__name__)
        else:
            self.noted.discard("save")

    def _touch_due(self) -> bool:
        return self.saved_at is None or _esom_mono() - self.saved_at >= _ESOM_TOUCH_EVERY

    # ----- one check --------------------------------------------------------

    async def poll(self) -> None:
        if self.polling:  # a check is already running: never run two at once
            log.debug("Xbox status monitor: a check is already running")
            return
        self.polling = True
        try:
            try:
                reading = await _esom_fetch_reading(None)
            except _EsomError as error:
                self._failed(error.kind)
                return
            self._recovered()
            events: List[Tuple[str, str]] = []
            for region in _ESOM_REGIONS:
                status, word = reading.status[region], reading.word[region]
                if status != "unknown":
                    self.odd[region] = None
                elif self.odd[region] != word:  # logged once for each unclear word, and again if it comes back after a clear reading
                    self.odd[region] = word
                    log.warning("Xbox status monitor: XBOX %s shows %r, which is not Online or Offline, so nothing is announced for it.", region, word)
                event = self.servers[region].feed(status, reading.at)
                if event is not None:
                    events.append((region, event))
            if events or self._touch_due():
                await self._save(reading.at)  # saved BEFORE anything is posted, so a restart can't repeat an announcement
            for region, event in events:
                if event == "baseline":
                    log.info("Xbox status monitor: XBOX %s is %s (the starting point; nothing is announced).", region, self.servers[region].state)
                    continue
                log.info("Xbox status monitor: XBOX %s is now %s.", region, event)
                try:
                    await self.announce(region, event)
                except asyncio.CancelledError:
                    raise
                except Exception:
                    log.exception("Xbox status monitor: the XBOX %s announcement failed", region)
        finally:
            self.polling = False

    def _failed(self, kind: str) -> None:
        self.fails += 1
        for server in self.servers.values():
            server.miss()
        if self.fails == 1:
            log.warning("Xbox status monitor: the check failed (%s). The last known status is kept and nothing is announced.", kind)
        elif self.fails % 30 == 0:
            log.warning("Xbox status monitor: still failing after %d checks in a row (%s).", self.fails, kind)

    def _recovered(self) -> None:
        if self.fails:
            log.info("Xbox status monitor: the page can be read again after %d failed check(s).", self.fails)
        self.fails = 0

    # ----- announcing -------------------------------------------------------

    async def announce(self, region: str, direction: str) -> None:
        """Post one confirmed change in the one allowed channel. Only "up" can ping, and only its own region's role."""
        now = _esom_mono()
        self.sent[region] = [moment for moment in self.sent[region] if now - moment < 3600]
        if len(self.sent[region]) >= _ESOM_MAX_PER_HOUR:
            log.warning("Xbox status monitor: not announcing XBOX %s %s: %d announcements were already made for it in the last hour.", region, direction, _ESOM_MAX_PER_HOUR)
            return
        mode, _, _ = _esom_target()
        channel, problem = await _esom_destination(self.bot, mode)
        if channel is None:
            log.warning("Xbox status monitor: not announcing XBOX %s %s: %s.", region, direction, problem)
            return
        role = None
        if direction == "up":
            role, why, serious = _esom_pick_role(channel, region, live=(mode == "live"))
            if role is None:
                log.log(logging.WARNING if serious else logging.INFO, "Xbox status monitor: XBOX %s is announced without a ping: %s.", region, why)
        text, embed, allowed = _esom_message(region, direction, role)
        try:
            await asyncio.wait_for(channel.send(content=text, embed=embed, allowed_mentions=allowed), _ESOM_SEND_TIMEOUT)
        except asyncio.TimeoutError:
            log.error("Xbox status monitor: Discord took too long to accept the XBOX %s %s announcement; it will not be retried.", region, direction)
            return
        except discord.HTTPException as error:
            log.error("Xbox status monitor: Discord refused the XBOX %s %s announcement (HTTP %s); it will not be retried.", region, direction, getattr(error, "status", "?"))
            return
        self.sent[region].append(now)
        log.info("Xbox status monitor: announced XBOX %s %s%s.", region, direction, " with a ping" if role is not None else "")

    # ----- the loop ---------------------------------------------------------

    def delay(self) -> float:
        """Seconds until the next check: the interval, doubling while checks keep failing (up to a limit)."""
        if self.fails <= 1:
            return self.interval
        return min(self.interval * 2 ** (self.fails - 1), max(self.interval, _ESOM_BACKOFF_CAP))

    async def _sleep(self, seconds: float) -> None:
        """Sleep in short slices so the monitor notices at once that the bot is shutting down."""
        end = _esom_mono() + seconds
        while not self.bot.is_closed():
            left = end - _esom_mono()
            if left <= 0:
                return
            await asyncio.sleep(min(left, _ESOM_SLEEP_SLICE))

    async def run(self) -> None:
        try:
            await self.bot.wait_until_ready()
            log.info("Xbox status monitor started: checking XBOX EU and XBOX NA every %s seconds.", self.interval)
            try:
                self.restore()
            except Exception:
                log.exception("Xbox status monitor: its saved status could not be used; a fresh baseline will be taken")
                self.servers = {region: _EsomServer(region) for region in _ESOM_REGIONS}
            try:
                await self.check_destination()
            except asyncio.CancelledError:
                raise
            except Exception:
                log.exception("Xbox status monitor: could not check where announcements will go")
            while not self.bot.is_closed():
                try:
                    await self.poll()
                except asyncio.CancelledError:
                    raise
                except Exception:
                    log.exception("Xbox status monitor: unexpected error (it keeps going)")
                await self._sleep(self.delay())
        except asyncio.CancelledError:
            raise
        except Exception:
            log.exception("Xbox status monitor stopped because of an unexpected error")
        finally:
            log.info("Xbox status monitor stopped")


# ----- the category name: one coloured circle for each megaserver ---------------------------------------------------------

_ESOM_CIRCLES = {"up": "🟢", "down": "🔴"}  # what the name shows for each confirmed status
_ESOM_CATEGORY_TEMPLATE = "Xbox EU {eu}┊{na} Xbox NA"  # the one standard layout of the category's name, every space and character included


def _esom_category_name(eu: str, na: str) -> Optional[str]:
    """The standard name of the category for these two statuses ("Xbox EU 🟢┊🟢 Xbox NA"), or None if either isn't up or down."""
    if eu not in _ESOM_CIRCLES or na not in _ESOM_CIRCLES:
        return None
    return _ESOM_CATEGORY_TEMPLATE.format(eu=_ESOM_CIRCLES[eu], na=_ESOM_CIRCLES[na])


class _EsomCategory:
    """Keeps the status category's name at the standard layout, "Xbox EU 🟢┊🟢 Xbox NA", its two circles (EU first, NA second) showing the
    statuses the monitor has confirmed. A name that somebody has changed by hand is put back within seconds: every tick the name the bot last
    gave the category is compared with the bot's own copy of the category (nothing is asked of Discord), and a difference is renamed back.
    A combination of statuses must stand for _ESOM_CATEGORY_DELAY seconds before the category is renamed, so the rename comes after the
    announcement rather than with it, and EU and NA changing one after the other is a single rename. It reads the monitor's confirmed
    statuses and nothing else, and does nothing until both are known. A name that is already right is not touched (so a restart leaves
    no audit-log entry), and a rename that could not be done is tried again later, never in a rapid loop."""

    def __init__(self, client: Any, monitor: Any) -> None:
        self.bot = client
        self.monitor = monitor
        self.wanted: Optional[Tuple[str, str]] = None  # the (EU, NA) statuses seen last
        self.since = 0.0  # when `wanted` was first seen (monotonic)
        self.applied: Optional[Tuple[str, str]] = None  # the (EU, NA) statuses the name was last made (or found) to show
        self.retry_at = 0.0  # no attempt before this (monotonic)
        self.quiet_until = 0.0  # no check for a hand-made change before this (monotonic): the bot's own copy of the name lags a moment behind its rename
        self.repairs: List[float] = []  # when the name was last put back after a hand-made change (monotonic), for the hourly limit
        self.capped = False  # whether the hourly limit has been reported
        self.problem = ""  # why the last attempt failed, so each reason is logged once

    def _statuses(self) -> Optional[Tuple[str, str]]:
        eu, na = (self.monitor.servers[region].state for region in _ESOM_REGIONS)
        return (eu, na) if eu in _ESOM_CIRCLES and na in _ESOM_CIRCLES else None

    async def _find(self) -> Tuple[Optional[Any], str]:
        """The category, if it can be renamed right now, or (None, why not)."""
        category_id, guild_id = _esom_id(ESO_STATUS_CATEGORY_ID), _esom_id(ESO_STATUS_MAIN_GUILD_ID)
        channel = self.bot.get_channel(category_id)
        if channel is None:
            try:
                channel = await self.bot.fetch_channel(category_id)
            except discord.NotFound:
                return None, "that category does not exist"
            except discord.Forbidden:
                return None, "the bot cannot see that category"
            except discord.HTTPException:
                return None, "Discord did not answer when the category was looked up"
        if not isinstance(channel, discord.CategoryChannel) or getattr(channel, "id", None) != category_id:
            return None, "that ID is not a category"
        if getattr(getattr(channel, "guild", None), "id", None) != guild_id:
            return None, "that category is not in the main server"
        me = getattr(channel.guild, "me", None)
        if me is not None and not channel.permissions_for(me).manage_channels:
            return None, "the bot does not have the Manage Channels permission for that category"
        return channel, ""

    def _failed(self, why: str) -> None:
        self.retry_at = _esom_mono() + _ESOM_CATEGORY_RETRY
        if why != self.problem:
            self.problem = why
            log.warning("Xbox status category: its name is not being updated: %s. It will try again in %d minutes.", why, _ESOM_CATEGORY_RETRY // 60)

    def _drifted(self) -> bool:
        """True if the category, as the bot has it in its own copy (nothing is asked of Discord), no longer carries the name the bot last
        gave it, that is, somebody has renamed it by hand."""
        if self.applied is None:
            return False
        category = self.bot.get_channel(_esom_id(ESO_STATUS_CATEGORY_ID))
        if not isinstance(category, discord.CategoryChannel):
            return False
        return str(getattr(category, "name", "")) != _esom_category_name(*self.applied)

    async def tick(self) -> None:
        statuses = self._statuses()
        if statuses is None:  # a status is not known yet: leave the name alone
            return
        now = _esom_mono()
        if statuses != self.wanted:
            self.wanted, self.since = statuses, now
        repair = False
        if statuses != self.applied and now - self.since >= _ESOM_CATEGORY_DELAY:
            target = statuses  # a change has stood long enough: the name follows it
        elif self.applied is not None and now >= self.quiet_until and self._drifted():
            target, repair = self.applied, True  # nothing new, but somebody has renamed the category: the standard name goes straight back
        else:
            return
        if now < self.retry_at:
            return
        if repair:
            self.repairs = [when for when in self.repairs if now - when < 3600]
            if len(self.repairs) >= _ESOM_CATEGORY_REPAIRS_PER_HOUR:
                if not self.capped:
                    self.capped = True
                    log.warning("Xbox status category: its name has been changed by hand %d times in the last hour, so it will not be put back again until that hour is up (a status change still renames it).", len(self.repairs))
                return
            self.capped = False
        category, why = await self._find()
        if category is None:
            self._failed(why)
            return
        name = _esom_category_name(*target)
        current = str(getattr(category, "name", ""))
        if name is None:  # (cannot happen: both statuses are up or down)
            return
        if name != current:
            reason = f"Xbox status: EU {target[0]}, NA {target[1]}" + (" (name changed by hand, put back)" if repair else "")
            try:
                await asyncio.wait_for(category.edit(name=name, reason=reason), _ESOM_CATEGORY_TIMEOUT)
            except asyncio.TimeoutError:
                self._failed("Discord took too long (it allows only two renames of one channel in ten minutes)")
                return
            except discord.Forbidden:
                self._failed("Discord refused the rename (the bot needs the Manage Channels permission for that category)")
                return
            except discord.HTTPException as error:
                self._failed(f"Discord refused the rename (HTTP {getattr(error, 'status', '?')})")
                return
            expected = _esom_category_name(*self.applied) if self.applied is not None else None
            if expected is not None:
                by_hand = current != expected  # (the name was last made to show these statuses, so anything else is somebody's edit)
            else:  # (just started: a name that is one of the four standard ones is simply from before the restart)
                by_hand = current not in {_ESOM_CATEGORY_TEMPLATE.format(eu=a, na=b) for a in _ESOM_CIRCLES.values() for b in _ESOM_CIRCLES.values()}
            log.info("Xbox status category: renamed to “%s”%s.", name, " (it had been changed by hand, so the standard layout is back)" if by_hand else "")
            self.quiet_until = _esom_mono() + _ESOM_CATEGORY_QUIET
            if repair:
                self.repairs.append(now)
        if self.problem:
            log.info("Xbox status category: its name can be updated again.")
            self.problem = ""
        self.applied = target

    async def _sleep(self, seconds: float) -> None:
        """Sleep in short slices so the updater notices at once that the bot is shutting down."""
        end = _esom_mono() + seconds
        while not self.bot.is_closed():
            left = end - _esom_mono()
            if left <= 0:
                return
            await asyncio.sleep(min(left, _ESOM_SLEEP_SLICE))

    async def run(self) -> None:
        try:
            await self.bot.wait_until_ready()
            log.info("Xbox status category: its name will follow the two statuses, %d seconds after a change is confirmed, and is put back within seconds if somebody renames it.", _ESOM_CATEGORY_DELAY)
            while not self.bot.is_closed():
                try:
                    await self.tick()
                except asyncio.CancelledError:
                    raise
                except Exception:
                    log.exception("Xbox status category: unexpected error (it keeps going)")
                await self._sleep(_ESOM_CATEGORY_TICK)
        except asyncio.CancelledError:
            raise
        except Exception:
            log.exception("Xbox status category updater stopped because of an unexpected error")
        finally:
            log.info("Xbox status category updater stopped")


_esom_category_task: Optional[asyncio.Task] = None


def _esom_start_category(monitor: Any) -> None:
    """Start the category updater for this monitor, if it is switched on: the category's ID is set, and the bot is live in the main server."""
    global _esom_category_task
    if not _esom_id(ESO_STATUS_CATEGORY_ID):
        return
    if not _ESOM_LIVE or not _esom_id(ESO_STATUS_MAIN_GUILD_ID):
        log.info("Xbox status category: not updated in test mode (it needs ESO_STATUS_LIVE on and the main server's ID).")
        return
    if _esom_category_task is not None and not _esom_category_task.done():
        _esom_category_task.cancel()
    _esom_category_task = asyncio.create_task(_EsomCategory(bot, monitor).run(), name="eso-status-category")


_esom_task: Optional[asyncio.Task] = None
_esom_synced = False


async def _esom_sync_commands() -> None:
    """Register /server (and /server-sim) in the servers they belong to. The bot's own start-up only syncs global commands, and
    these are deliberately not global. Done once per run; a failure is logged and the rest of the bot carries on."""
    global _esom_synced
    if _esom_synced:
        return
    _esom_synced = True
    for guild_id in _esom_command_guilds():
        try:
            synced = await bot.tree.sync(guild=discord.Object(id=guild_id))
            log.info("Xbox status: registered %d command(s) in server %s.", len(synced), guild_id)
        except discord.HTTPException as error:
            log.warning("Xbox status: could not register its commands in server %s (HTTP %s). Check the ID, that the bot is in that server and that it was invited with the applications.commands scope.", guild_id, getattr(error, "status", "?"))


@bot.listen("on_ready")
async def eso_status_ready():
    """Register the commands and start the monitor, once. on_ready fires again after every reconnect, so a monitor that is
    already running is kept."""
    global _esom_task
    try:
        await _esom_sync_commands()
    except Exception:
        log.exception("Xbox status: the commands could not be registered")
    try:
        if not _ESOM_ENABLED:
            log.info("Xbox status monitor is switched off (the ESO_STATUS_MONITOR setting is off).")
        elif _esom_task is None or _esom_task.done():
            problem = _esom_config_problem()
            if problem:
                log.warning("Xbox status monitor is off, and nothing will be announced anywhere: %s.", problem)
            else:
                monitor = _EsomMonitor(bot, _ESOM_INTERVAL, _ESOM_STATE_FILE)
                _esom_task = asyncio.create_task(monitor.run(), name="eso-status-monitor")
                _esom_start_category(monitor)
    except Exception:
        log.exception("The Xbox status monitor could not be started")


# ----- /server and /server-sim ---------------------------------------------------------------------------------------

def _esom_commands_line(interaction: Any) -> str:
    """The /commands line for /server. It is shown only in the servers where /server exists, so nobody is told about a command
    they don't have."""
    if getattr(interaction, "guild_id", None) in _esom_command_guilds():
        return "`/server` -- Checks whether the ESO Xbox EU or Xbox NA megaserver is up or down right now.\n"
    return ""


async def _esom_lookup() -> Tuple[Optional[_EsomReading], str]:
    """What /server should show: (the reading, "") if it is fresh, or (the newest reading there is, why a fresh one couldn't be taken)."""
    try:
        return await _esom_fetch_reading(_ESOM_CACHE_SECONDS), ""
    except _EsomError as error:
        return _ESOM_LATEST, error.kind


_ESOM_REGION_CHOICES = [app_commands.Choice(name="Xbox EU", value="EU"), app_commands.Choice(name="Xbox NA", value="NA")]

# Registered ONLY for the servers in _esom_command_guilds(). (A command registered for an empty list of servers would be
# global, which is exactly what must not happen, hence the "if".)
if _esom_command_guilds():

    @bot.tree.command(
        name="server", description="Check whether an ESO Xbox megaserver is up or down.",
        guilds=[discord.Object(id=guild_id) for guild_id in _esom_command_guilds()],
    )
    @app_commands.describe(region="Which Xbox megaserver to check.")
    @app_commands.choices(region=_ESOM_REGION_CHOICES)
    async def eso_server_command(interaction: discord.Interaction, region: app_commands.Choice[str]):
        none = discord.AllowedMentions.none()
        if interaction.guild_id not in _esom_command_guilds() or region.value not in _ESOM_REGIONS:
            await interaction.response.send_message("This command isn’t switched on in this server.", ephemeral=True, allowed_mentions=none)
            return
        # Reading the page can take a few seconds and Discord only waits 3 for a first answer, so say "working on it" first.
        await interaction.response.defer()
        try:
            reading, problem = await _esom_lookup()
            embed = _esom_status_embed(region.value, reading, not problem, _esom_now())
        except Exception as error:
            log.error("/server: unexpected %s while checking the status:\n%s", type(error).__name__, "".join(traceback.format_tb(error.__traceback__)).rstrip())
            await interaction.followup.send("Something went wrong checking the server status.", allowed_mentions=none)
            return
        if problem:
            log.warning("/server: no fresh reading could be taken (%s)", problem)
        # Nothing here touches the monitor's saved status, announces anything or pings anyone: it only reads and replies.
        await interaction.followup.send(embed=embed, allowed_mentions=none)


if _esom_id(ESO_STATUS_TEST_GUILD_ID):

    @bot.tree.command(
        name="server-sim", description="Test server only: post a simulated Xbox status change in the test channel.",
        guilds=[discord.Object(id=_esom_id(ESO_STATUS_TEST_GUILD_ID))],
    )
    @app_commands.describe(region="Which Xbox megaserver to simulate.", event="What to simulate.")
    @app_commands.choices(
        region=_ESOM_REGION_CHOICES,
        event=[
            app_commands.Choice(name="Server goes down", value="down"),
            app_commands.Choice(name="Server comes back up (nobody is pinged)", value="up"),
            app_commands.Choice(name="Server comes back up, with a real test ping", value="ping"),
        ],
    )
    @app_commands.default_permissions(manage_guild=True)
    @app_commands.checks.has_permissions(manage_guild=True)
    async def eso_server_sim_command(interaction: discord.Interaction, region: app_commands.Choice[str], event: app_commands.Choice[str]):
        none = discord.AllowedMentions.none()
        if interaction.guild_id != _esom_id(ESO_STATUS_TEST_GUILD_ID) or region.value not in _ESOM_REGIONS or event.value not in ("down", "up", "ping"):
            await interaction.response.send_message("This command only works in the test server.", ephemeral=True, allowed_mentions=none)
            return
        await interaction.response.defer(ephemeral=True)
        direction = "down" if event.value == "down" else "up"
        try:
            channel, problem = await _esom_destination(bot, "test")  # the test channel, whatever mode the monitor is in
            if channel is None:
                await interaction.followup.send(f"Nothing was posted: {problem}.", ephemeral=True, allowed_mentions=none)
                return
            role, note = None, ""
            if event.value == "ping":
                if not _ESOM_TEST_PINGS:
                    await interaction.followup.send("Nothing was posted: test pings are switched off. Set ESO_STATUS_TEST_PINGS to on to use this one.", ephemeral=True, allowed_mentions=none)
                    return
                role, why, _ = _esom_pick_role(channel, region.value, live=False)
                if role is None:
                    await interaction.followup.send(f"Nothing was posted, because no role could be pinged: {why}.", ephemeral=True, allowed_mentions=none)
                    return
            elif event.value == "up":  # check the role the way a real restoration would, without pinging it
                checked, why, _ = _esom_pick_role(channel, region.value, live=False, gate=False)
                if checked is None:
                    note = f"Nobody was pinged, and a real restoration would not ping anyone: {why}."
                else:
                    shown = discord.utils.escape_markdown(discord.utils.escape_mentions(str(getattr(checked, "name", "") or "the role")))
                    if _ESOM_TEST_PINGS:
                        note = f"Nobody was pinged. A real restoration in this server would ping the role “{shown}”."
                    else:
                        note = f"Nobody was pinged. The role “{shown}” is fine, but test pings are off (ESO_STATUS_TEST_PINGS), so a real restoration in this server would not ping anyone."
            else:
                note = "Nobody was pinged (a real outage never pings anyone)."
            text, embed, allowed = _esom_message(region.value, direction, role, simulated=True, note=note)
            await asyncio.wait_for(channel.send(content=text, embed=embed, allowed_mentions=allowed), _ESOM_SEND_TIMEOUT)
        except (discord.HTTPException, asyncio.TimeoutError) as error:
            log.warning("/server-sim: the simulated message could not be posted (%s)", getattr(error, "status", type(error).__name__))
            await interaction.followup.send("Discord didn’t accept the message. Check the bot’s permissions in the test channel.", ephemeral=True, allowed_mentions=none)
            return
        except Exception as error:
            log.error("/server-sim: unexpected %s:\n%s", type(error).__name__, "".join(traceback.format_tb(error.__traceback__)).rstrip())
            await interaction.followup.send("Something went wrong with the simulation.", ephemeral=True, allowed_mentions=none)
            return
        # Nothing above touches the monitor, its saved status or the real announcement path: it only posts a labelled message.
        await interaction.followup.send(f"Posted a simulated XBOX {region.value} “{direction}” message in #{getattr(channel, 'name', 'the test channel')}. {note}".strip(), ephemeral=True, allowed_mentions=none)


# --------------------------------------------------------------------------
# /roster
#
# A short, paged guide to using the roster. Anyone can run it, and it is posted
# publicly in the channel it was used in. Only the person who ran it can press
# its buttons, so nobody can flip the page out from under someone who is
# reading (anyone else can simply run /roster to open their own copy).
#
# Every page -- its title, text, screenshot and button name -- is written in
# ROSTER_PAGES below. To change the guide, edit that list: nothing else in this
# section needs touching.
# --------------------------------------------------------------------------

_ROSTER_TIMEOUT = 300  # seconds after the last button press before the buttons are taken away
_ROSTER_COLOUR = 0x3498DB  # the stripe down the side of the embed


class _RosterPage:
    """One page of the /roster guide."""

    def __init__(self, button: str, title: str, text: str, image: Optional[str] = None) -> None:
        self.button = button  # the name on the buttons that lead TO this page
        self.title = title
        self.text = text
        self.image = image  # a link that opens straight to a screenshot, or None for a page without one


# The pages, in order. A page's button name is what the buttons on the pages either side of it say when
# they lead here (so page one's "Introduction" is the back button on page two). Discord's limits: a
# button name can be up to 80 characters (a few words reads best on a phone), a title up to 256, and the
# text up to 4096. The text can use Discord's formatting, such as *italics* and **bold**.
ROSTER_PAGES = [
    _RosterPage(
        button="Introduction",
        title="How to use the roster",
        text=(
            "The roster will be posted the night before a group so everyone can select their "
            "preferred role and gear setup ahead of time.\n\n"
            "This allows us to better optimise the group composition, and ensure we have the "
            "right balance of roles and builds for the main group."
        ),
    ),
    _RosterPage(
        button="How to sign up",
        title="How to sign up",
        text=(
            "Each roster will have two parts: the first embed allows you to choose your role within the "
            "group (Puller, Damage Dealer, Healer or Support), while the second allows you to "
            "select your unique buffs, skills and monster sets.\n\n"
            "To secure your position in the group, you must interact with the first part."
        ),
        image="https://cdn.discordapp.com/attachments/946061620487024640/1564064526822015016/IMG_6011.png",
    ),
    _RosterPage(
        button="How to choose your role",
        title="How to choose your role",
        text="On the top embed, click the ‘*Select your class.*’",
        image="https://cdn.discordapp.com/attachments/946061620487024640/1564065912901074964/IMG_6015.png",
    ),
    _RosterPage(
        button="Classes",
        title="Classes",
        text=(
            "Choose the group role you wish to play. If you want to secure your position in the group, "
            "but aren’t sure on what to play: choose *Reserved*."
        ),
        image="https://cdn.discordapp.com/attachments/946061620487024640/1564067145912942652/IMG_6012.png",
    ),
    _RosterPage(
        button="Specifications",
        title="Specifications",
        text=(
            "After selecting your role, scroll down to the very bottom of the channel and a new menu "
            "will have appeared. This is where you can choose your gear. Once selected, your name will "
            "appear in the roster with your chosen specs."
        ),
        image="https://cdn.discordapp.com/attachments/946061620487024640/1564071110860079256/IMG_6013.png",
    ),
    _RosterPage(
        button="Group selections",
        title="Group selections",
        text=(
            "To see what other people are running, you can click on the small helmet emoji next to "
            "their name. This will show you what set they have chosen.\n\n"
            "Please note that some sets, particularly Healer sets, can only be chosen once."
        ),
        image="https://cdn.discordapp.com/attachments/946061620487024640/1564211456977801216/IMG_6016.jpg",
    ),
    _RosterPage(
        button="Buffs and Skills",
        title="Buffs and Skills",
        text=(
            "After choosing your role, the second part of the roster becomes available. Only after your "
            "position is secured can this be interacted with. It’s a way for you to choose unique buffs "
            "and skills (Minor Toughness, Expansive Frost Cloak) that are ordinarily difficult to pin to "
            "an individual role. You can also select certain monster sets."
        ),
        image="https://cdn.discordapp.com/attachments/946061620487024640/1564072398993498123/IMG_6014.png",
    ),
]


def _roster_embed(index: int, reader: str) -> discord.Embed:
    page = ROSTER_PAGES[index]
    embed = discord.Embed(title=page.title, description=page.text, colour=discord.Colour(_ROSTER_COLOUR))
    if page.image:
        embed.set_image(url=page.image)
    # A footer is plain text (no mentions or formatting), so this shows their name rather than pinging them.
    embed.set_footer(text=f"Only {reader} can use these buttons, but anyone can use /roster.")
    return embed


def _roster_buttons(index: int) -> List[Tuple[int, Any]]:
    """The buttons under page `index`, left to right, as (page the button leads to, its colour).

    A grey button back to the page before it (page one has nothing before it, so it has none), then a
    blue button on to the page after it (the last page has nothing after it, so it has none). Each
    button is named after the page it leads to."""
    last = len(ROSTER_PAGES) - 1
    plan: List[Tuple[int, Any]] = []
    if index > 0:
        plan.append((index - 1, discord.ButtonStyle.secondary))
    if index < last:
        plan.append((index + 1, discord.ButtonStyle.primary))
    return plan


class _RosterView(discord.ui.View):
    """The buttons under /roster. Everyone can read the message, but only the person who ran /roster can
    press the buttons."""

    def __init__(self, reader: Any) -> None:
        super().__init__(timeout=_ROSTER_TIMEOUT)
        self.reader_id = reader.id
        self.reader_name = reader.display_name
        self.index = 0  # which page is showing
        # The newest interaction on this message (the /roster command itself, then each button press). When
        # the buttons time out there is no new interaction to answer, so this is used to take them away.
        self.latest: Optional[discord.Interaction] = None
        self._add_buttons()

    def _add_buttons(self) -> None:
        self.clear_items()
        for target, style in _roster_buttons(self.index):
            button = discord.ui.Button(label=ROSTER_PAGES[target].button, style=style)
            button.callback = self._go_to(target)
            self.add_item(button)

    def _go_to(self, target: int) -> Any:
        async def callback(interaction: discord.Interaction) -> None:
            self.index = target
            self.latest = interaction
            self._add_buttons()
            await interaction.response.edit_message(embed=_roster_embed(target, self.reader_name), view=self)

        return callback

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.reader_id:
            await interaction.response.send_message(
                f"Only {discord.utils.escape_markdown(self.reader_name)} can use these buttons. "
                "Run /roster to open your own copy of the guide.",
                ephemeral=True,
                allowed_mentions=discord.AllowedMentions.none(),
            )
            return False
        return True

    async def on_timeout(self) -> None:
        # Nobody has pressed a button for a while: take the buttons away. The guide itself stays on the
        # message, on whichever page it was left.
        if self.latest is None:
            return
        try:
            await self.latest.edit_original_response(view=None)
        except Exception:
            log.warning("/roster: could not take the buttons away after the timeout", exc_info=True)

    async def on_error(self, interaction: discord.Interaction, error: Exception, item: discord.ui.Item) -> None:
        log.error("Unhandled error in the /roster buttons", exc_info=error)
        text = "Something went wrong with that button."
        try:
            if interaction.response.is_done():
                await interaction.followup.send(text, ephemeral=True)
            else:
                await interaction.response.send_message(text, ephemeral=True)
        except Exception:
            log.warning("/roster: could not tell the user that a button failed", exc_info=True)


@bot.tree.command(name="roster", description="How to use the roster and sign up for a group.")
@app_commands.guild_only()
async def roster(interaction: discord.Interaction):
    # Public on purpose (no ephemeral=True): everyone in the channel can see the guide. The buttons are
    # the part that belongs to one person -- see _RosterView.interaction_check.
    view = _RosterView(interaction.user)
    view.latest = interaction
    await interaction.response.send_message(
        embed=_roster_embed(0, view.reader_name), view=view, allowed_mentions=discord.AllowedMentions.none(),
    )


# --------------------------------------------------------------------------
# ESO Patch Notes watcher
#
# What it does
#   Every few minutes it asks the ESO forum for the newest threads in the Patch Notes category
#   (https://forums.elderscrollsonline.com/en/categories/patch-notes) and announces each NEW thread once, with a link and the
#   first lines of the post, in the same channel as the Xbox status announcements. The announcement is the thread's title as a
#   link, with a 📜 in front and a blue bar, or a 🔧 and an orange bar when the title says hotfix. Only threads are watched, not
#   replies to older threads. A hotfix is announced like any other thread in that category. For threads that were already there
#   when it first started it posts nothing, except the single newest one if it is younger than ESO_PATCH_NOTES_FIRST_RUN_HOURS,
#   so that a post made just before the bot started is not lost.
#
# Where it reads
#   The forum's own API, https://forums.elderscrollsonline.com/api/v2/..., the same data the forum's pages are built from.
#   Nothing here logs in and nothing is ever written to the forum. It talks to that one address only, over https (a redirect
#   anywhere else counts as a failed check), about once every ESO_PATCH_NOTES_INTERVAL_SECONDS (300 unless changed), and
#   waits longer while the forum keeps failing or asks to be left alone (HTTP 429 with a Retry-After).
#   The category is found by asking the forum for its list of categories and taking the one whose address name is
#   "patch-notes"; its number is then kept in the saved file. ESO_PATCH_NOTES_CATEGORY_ID (just below) skips that look-up.
#
# Where it posts
#   Wherever the Xbox status announcements go (_esom_target and _esom_destination): while ESO_STATUS_LIVE is on, the main
#   server's announcement channel (ESO_STATUS_MAIN_CHANNEL_ID), otherwise the test channel. If that place doesn't check out,
#   nothing is posted and the log says why. An announcement never pings anyone.
#
# What it remembers
#   A small file (/data/eso_patch_notes_state.json on FadeHost): the number of the category and the numbers of the threads it
#   has dealt with. A thread is added when it has been announced (or skipped for being more than a week old), so a restart never
#   repeats one, and a post that Discord refuses is tried again at the next check (three tries, then it is given up on and the
#   owner is told). A file that can't be read is set aside, never overwritten, and the first look starts again.
#
# When something is wrong
#   A check that fails (the forum is down, answers with an error, or gives an answer that doesn't look like threads) changes
#   nothing and announces nothing. After three failed checks in a row Poss Bot posts a ⚠️ warning in ESO_OBSERVER_CHANNEL_ID,
#   pinging ESO_OBSERVER_PING_USER_ID, at most once an hour, and a ✅ when the forum can be read again. The first look after a
#   fresh start is reported there too, so it is plain that the watcher works. ESO_PATCH_NOTES=off stops the whole watcher.
# --------------------------------------------------------------------------

ESO_PATCH_NOTES_CATEGORY_ID = 0  # 0 = find the Patch Notes category by itself (recommended); otherwise the forum's own number for it
ESO_PATCH_NOTES_FIRST_RUN_HOURS = 36  # at the very first start, announce the newest thread if it is younger than this many hours (0 = announce nothing then)

_EPN_ENABLED = _esom_flag("ESO_PATCH_NOTES", True)  # off switches the whole watcher off
try:
    _EPN_INTERVAL = min(3600, max(120, int(os.environ.get("ESO_PATCH_NOTES_INTERVAL_SECONDS", "300"))))
except ValueError:
    _EPN_INTERVAL = 300
# Where the saved list is kept: ESO_PATCH_NOTES_STATE_PATH if set, else /data when that folder exists, else next to this script.
_EPN_STATE_FILE = Path(
    os.environ.get("ESO_PATCH_NOTES_STATE_PATH")
    or (Path("/data/eso_patch_notes_state.json") if Path("/data").is_dir() else Path(__file__).parent / "eso_patch_notes_state.json")
)

_EPN_API = "https://forums.elderscrollsonline.com/api/v2"
_EPN_SITE = "https://forums.elderscrollsonline.com"
_EPN_HOSTS = ("forums.elderscrollsonline.com",)  # a request or a redirect may only go to this host...
_EPN_SCHEMES = ("https",)  # ...over https
_EPN_CATEGORY_CODE = "patch-notes"  # the category's address name: .../categories/patch-notes
_EPN_CATEGORY_NAME = "patch notes"  # its visible name, used only if nothing has the address name above
_EPN_CATEGORY_PAGES = 10  # the most pages (of 100 categories) looked through when finding the category
_EPN_LIST_LIMIT = 10  # how many of the newest threads are asked for at each check
_EPN_TIMEOUT = 10  # seconds the forum gets for each step of a request
_EPN_TOTAL_TIMEOUT = 25  # seconds for a whole request, reading the answer included
_EPN_MAX_BYTES = 4_000_000  # the most that is read from one answer (and the most it may unpack to)
_EPN_MAX_AGE = 7 * 24 * 3600  # seconds; a thread older than this that only now turns up is skipped, not announced
_EPN_MAX_PER_RUN = 5  # the most announcements made at one check (the rest wait for the next)
_EPN_MAX_PER_HOUR = 10  # the most announcements in an hour, however many threads turn up
_EPN_SEEN_KEEP = 200  # how many thread numbers are remembered
_EPN_SEND_TRIES = 3  # how many times Discord may refuse one announcement before it is given up on
_EPN_SEND_TIMEOUT = 30  # seconds Discord gets to accept a message
_EPN_FAILS_BEFORE_WARNING = 3  # failed checks in a row before the owner is warned
_EPN_WARN_EVERY = 3600  # seconds; the same kind of warning is not repeated sooner than this
_EPN_BACKOFF_CAP = 900  # seconds; the longest wait between checks while the forum keeps failing
_EPN_SLEEP_SLICE = 5  # seconds; the watcher sleeps in slices this long so it notices at once that the bot is closing
_EPN_TEASER_CHARS = 400  # how much of the post is shown under the title
_EPN_BLUE, _EPN_ORANGE = 0x3498DB, 0xE67E22  # patch notes, hotfix
_EPN_HOTFIX = re.compile(r"\bhot[\s\-]*fix", re.IGNORECASE)
# Characters that are never wanted in text taken from the forum: control characters, line and paragraph separators, and the
# characters that can make text run backwards or hide other text.
_EPN_CONTROL = re.compile("[\x00-\x1f\x7f\u2028\u2029\u202a-\u202e\u2066-\u2069]")
_EPN_BREAKS = re.compile(r"(?i)<\s*(?:br\s*/?|/\s*(?:p|div|li|ul|ol|h[1-6]|tr|blockquote))\s*>")


def _epn_now() -> datetime:
    return _utcnow()


def _epn_mono() -> float:
    return time.monotonic()


def _epn_first_run_seconds() -> float:
    """How young the newest thread must be to be announced at the very first start, in seconds (0 = never)."""
    hours = ESO_PATCH_NOTES_FIRST_RUN_HOURS
    if isinstance(hours, bool) or not isinstance(hours, (int, float)) or hours <= 0:
        return 0.0
    return float(hours) * 3600


# ----- reading the forum -----------------------------------------------------------------------------------------

class _EpnError(Exception):
    """A request or reading that gave nothing trustworthy. `kind` is short and plain and goes in the log; `detail` (optional) is
    a longer explanation for the warning to the owner; `wait` is how many seconds the forum asked to be left alone, if it did;
    `topic` says which warning this belongs to. None of them ever holds text from the forum's pages."""

    def __init__(self, kind: str, detail: str = "", wait: float = 0.0, topic: str = "read") -> None:
        super().__init__(kind)
        self.kind, self.detail, self.wait, self.topic = kind, detail, wait, topic


class _EpnRedirects(urllib.request.HTTPRedirectHandler):
    max_redirections = 3

    def redirect_request(self, req: Any, fp: Any, code: int, msg: str, headers: Any, newurl: str) -> Any:
        target = urllib.parse.urlsplit(newurl)
        if target.scheme not in _EPN_SCHEMES or (target.hostname or "").lower() not in _EPN_HOSTS:
            return None  # anywhere else counts as a failed check, not something to follow
        return super().redirect_request(req, fp, code, msg, headers, newurl)


def _epn_gunzip(data: bytes, limit: int) -> bytes:
    """Unpack a gzip-compressed answer, refusing to produce more than `limit` bytes (so a tiny file can't unpack into a huge one)."""
    import zlib

    decoder = zlib.decompressobj(16 + zlib.MAX_WBITS)  # 16 + ... = a gzip wrapper
    try:
        out = decoder.decompress(data, limit + 1)
    except zlib.error:
        raise _EpnError("the reply was damaged") from None
    if len(out) > limit:
        raise _EpnError("the reply is much bigger than expected")
    if not decoder.eof:
        raise _EpnError("connection dropped")  # the compressed answer stops before its end
    return out


def _epn_retry_after(headers: Any) -> float:
    """The seconds a Retry-After header asks for (at most an hour), or 0 if there is none or it isn't a plain number."""
    try:
        value = headers.get("retry-after") if headers is not None else None
    except Exception:
        return 0.0
    if isinstance(value, str) and value.strip().isascii() and value.strip().isdigit():
        return float(min(int(value.strip()), 3600))
    return 0.0


def _epn_read(response: Any, started: float) -> bytes:
    """The body of the answer, read up to the size limit and the overall time limit, and unpacked if it came gzip-compressed."""
    deadline = started + _EPN_TOTAL_TIMEOUT - 3
    chunks: List[bytes] = []
    size = 0
    take = getattr(response, "read1", response.read)  # read1 returns what has arrived, so a site that trickles can't hold this up
    while True:
        if time.monotonic() > deadline:
            raise _EpnError("timed out")
        chunk = take(65536)
        if not chunk:
            break
        chunks.append(chunk)
        size += len(chunk)
        if size > _EPN_MAX_BYTES:
            raise _EpnError("the reply is much bigger than expected")
    message = response.headers
    promised = message.get("content-length")
    if promised is not None and promised.strip().isascii() and promised.strip().isdigit() and size < int(promised):
        raise _EpnError("connection dropped")  # the forum hung up before the whole answer arrived
    body = b"".join(chunks)
    encoding = (message.get("content-encoding") or "identity").strip().lower()
    if encoding in ("gzip", "x-gzip"):
        return _epn_gunzip(body, _EPN_MAX_BYTES)
    if encoding not in ("", "identity"):
        raise _EpnError("the reply was compressed in a way I can't read")
    return body


def _epn_request(path: str) -> Any:
    """One GET of an API address, answered as parsed JSON. It blocks, so it runs in a worker thread. Raises _EpnError for anything
    that isn't a normal JSON answer."""
    started = time.monotonic()
    request = urllib.request.Request(_EPN_API + path, headers={
        "User-Agent": f"PossBot/1.0 (Discord bot; read-only ESO forum Patch Notes watcher; about one request every {_EPN_INTERVAL} seconds)",
        "Accept": "application/json",
        "Accept-Encoding": "gzip",
    })
    try:
        with urllib.request.build_opener(_EpnRedirects).open(request, timeout=_EPN_TIMEOUT) as response:
            status = response.status
            content_type = response.headers.get("content-type") or ""
            charset = response.headers.get_content_charset() or "utf-8"
            body = _epn_read(response, started)
    except urllib.error.HTTPError as error:  # 4xx, 5xx and a refused redirect: an answer, but not one to use
        wait = _epn_retry_after(error.headers)
        with contextlib.suppress(Exception):
            error.close()
        raise _EpnError(f"HTTP {error.code}", wait=wait) from None
    except _EpnError:
        raise
    except Exception as error:
        raise _EpnError(_esom_error_kind(error)) from None
    if status != 200:
        raise _EpnError(f"HTTP {status}")
    if "json" not in content_type.lower():
        raise _EpnError("the reply was not JSON")
    if charset.lower().replace("_", "-") in ("utf-8", "utf8"):
        charset = "utf-8-sig"  # (also accepts a byte-order mark at the start, which JSON must not have)
    try:
        text = body.decode(charset, errors="replace")
    except LookupError:  # a character set Python doesn't know
        text = body.decode("utf-8-sig", errors="replace")
    try:
        return json.loads(text)
    except (ValueError, RecursionError):
        raise _EpnError("the reply was not valid JSON") from None


async def _epn_fetch(path: str) -> Any:
    """Ask the forum for one API address in a worker thread, so the bot never waits for it. Raises _EpnError if there is no
    trustworthy answer."""
    try:
        return await asyncio.wait_for(asyncio.get_running_loop().run_in_executor(None, _epn_request, path), _EPN_TOTAL_TIMEOUT)
    except asyncio.TimeoutError:
        raise _EpnError("timed out") from None
    except _EpnError:
        raise
    except Exception:
        log.exception("Patch Notes watcher: the forum could not be read because of a fault in the watcher")
        raise _EpnError("a fault in the watcher (see the log)") from None


# ----- turning the forum's answer into threads -------------------------------------------------------------------

class _EpnThread:
    """One thread of the Patch Notes category as the forum described it. Every text in it is already safe to show."""

    def __init__(self, ident: int, title: str, url: str, posted: Optional[datetime], category_id: int, teaser: str) -> None:
        self.ident, self.title, self.url = ident, title, url
        self.posted, self.category_id, self.teaser = posted, category_id, teaser


def _epn_int(value: Any) -> int:
    """A positive whole number from the forum's JSON (a number, or text made only of digits), or 0 if it isn't one."""
    if isinstance(value, bool):
        return 0
    if isinstance(value, int):
        return value if value > 0 else 0
    if isinstance(value, str) and value.isascii() and value.isdigit() and len(value) <= 18:
        return int(value)
    return 0


def _epn_date(value: Any) -> Optional[datetime]:
    """The moment in a date such as "2026-10-28T20:14:03+00:00" (UTC if it says nothing), or None if it isn't one."""
    if not isinstance(value, str):
        return None
    text = value.strip()
    if text[-1:] in ("Z", "z"):
        text = text[:-1] + "+00:00"
    try:
        moment = datetime.fromisoformat(text)
    except ValueError:
        return None
    if moment.tzinfo is None:
        moment = moment.replace(tzinfo=timezone.utc)
    return moment.astimezone(timezone.utc)


def _epn_clean(value: Any, limit: int) -> str:
    """One line of plain text from something the forum sent: control characters gone, spaces tidied, cut to `limit` characters
    (ending in "…" if it was cut). Anything that isn't text gives ""."""
    if not isinstance(value, str):
        return ""
    text = " ".join(_EPN_CONTROL.sub(" ", value).split())
    if len(text) > limit:
        text = text[: max(0, limit - 1)].rstrip() + "…"
    return text


def _epn_strip_tags(text: str) -> str:
    """The text without its <tags>. One pass, so odd or hostile markup can't make it slow. A "<" that doesn't start a tag (as in
    "1 < 2") stays; a tag that is never closed takes the rest of the text with it."""
    parts: List[str] = []
    pos = 0
    while True:
        start = text.find("<", pos)
        if start < 0:
            parts.append(text[pos:])
            break
        parts.append(text[pos:start])
        after = text[start + 1:start + 2]
        if after and (after.isalpha() or after in "/!?"):
            end = text.find(">", start + 1)
            if end < 0:
                break
            pos = end + 1
        else:
            parts.append("<")
            pos = start + 1
    return "".join(parts)


def _epn_plain(raw: str, limit: int) -> str:
    """The readable start of a post that the forum gave as HTML: line breaks kept (one per paragraph), tags gone, character codes
    turned into characters, cut to `limit` characters at a word."""
    text = html.unescape(_epn_strip_tags(_EPN_BREAKS.sub("\n", raw[:20000])))
    lines = [" ".join(_EPN_CONTROL.sub(" ", line).split()) for line in text.split("\n")]
    text = "\n".join(line for line in lines if line)
    if len(text) > limit:
        room = max(1, limit - 1)  # (one character is kept for the "…")
        cut = text[:room]
        space = max(cut.rfind(" "), cut.rfind("\n"))
        if space >= room // 2:
            cut = cut[:space]
        text = cut.rstrip(" \n,.;:-–—") + "…"
    return text


def _epn_teaser(item: Dict[str, Any]) -> str:
    """The start of the post, for under the title: the forum's own short text if it sent one, otherwise the start of the post."""
    for key in ("excerpt", "body"):
        value = item.get(key)
        if isinstance(value, str) and value.strip():
            text = _epn_plain(value, _EPN_TEASER_CHARS)
            if len(text) >= 20:
                return text
    return ""


def _epn_thread_url(value: Any, ident: int) -> str:
    """The link to a thread: the one the forum gave, if it is an https address on the forum itself, otherwise the forum's own
    short address for that thread number (which the forum turns into the full one)."""
    if isinstance(value, str):
        link = value.strip()
        # Only plain address characters (no spaces, backslashes, quotes or angle brackets), and no "name@" in front of the host.
        if 0 < len(link) <= 1000 and re.fullmatch(r"[A-Za-z0-9\-._~:/?#\[\]@!$&'()*+,;=%]+", link):
            try:
                parts = urllib.parse.urlsplit(link)
                host = (parts.hostname or "").lower()
                plain = parts.username is None and parts.password is None and parts.port in (None, 443)
            except ValueError:
                parts, host, plain = None, "", False
            if parts is not None and plain and parts.scheme in _EPN_SCHEMES and host in _EPN_HOSTS:
                return link
    return f"{_EPN_SITE}/en/discussion/{ident}"


def _epn_threads(data: Any) -> List[_EpnThread]:
    """The threads in the forum's answer to a request for a list of discussions. Entries that are missing a number, a title or a
    category are left out. An answer that isn't a list, or a non-empty list in which nothing is usable, is an error: it means
    the forum's answer has changed shape, and nothing may be announced from it."""
    if not isinstance(data, list):
        raise _EpnError("the forum's answer was not a list of threads", topic="shape")
    threads: List[_EpnThread] = []
    taken: Set[int] = set()
    for item in data[:200]:
        if not isinstance(item, dict):
            continue
        ident = _epn_int(item.get("discussionID"))
        title = _epn_clean(item.get("name"), 256)
        category = _epn_int(item.get("categoryID"))
        if not ident or not title or not category or ident in taken:
            continue
        taken.add(ident)
        threads.append(_EpnThread(
            ident, title, _epn_thread_url(item.get("url"), ident), _epn_date(item.get("dateInserted")), category, _epn_teaser(item),
        ))
    if data and not threads:
        raise _EpnError("the forum's answer has a shape I don't recognise", topic="shape")
    return threads


def _epn_pick_category(data: Any) -> Tuple[int, List[str]]:
    """(the number of the Patch Notes category or 0, "name (number)" for each category seen) from the forum's list of categories.
    The category is the one whose address name is "patch-notes", else the one whose link ends that way, else the one called
    "Patch Notes". Categories nested inside others are looked through too."""
    by_code: List[int] = []
    by_link: List[int] = []
    by_name: List[int] = []
    names: List[str] = []
    stack: List[Any] = [data]
    visited = 0
    while stack and visited < 5000:
        item = stack.pop()
        if isinstance(item, list):
            stack.extend(reversed(item))  # (reversed, so they are looked at in the forum's own order)
            continue
        if not isinstance(item, dict):
            continue
        visited += 1
        children = item.get("children")
        if isinstance(children, list):
            stack.extend(reversed(children))
        ident = _epn_int(item.get("categoryID"))
        if not ident:
            continue
        name = _epn_clean(item.get("name"), 60)
        names.append(f"{name or '?'} ({ident})")
        code = item.get("urlcode")
        if isinstance(code, str) and code.strip().lower() == _EPN_CATEGORY_CODE:
            by_code.append(ident)
        link = item.get("url")
        if isinstance(link, str):
            try:
                last = urllib.parse.urlsplit(link.strip()).path.rstrip("/").rsplit("/", 1)[-1].lower()
            except ValueError:
                last = ""
            if last == _EPN_CATEGORY_CODE:
                by_link.append(ident)
        if name.lower() == _EPN_CATEGORY_NAME:
            by_name.append(ident)
    for found in (by_code, by_link, by_name):
        if found:
            return min(found), names
    return 0, names


# ----- the announcement ---------------------------------------------------------------------------------------------

def _epn_safe(text: str) -> str:
    """Text from the forum made safe to put in a Discord message: mentions defused, markdown characters shown as they are."""
    return discord.utils.escape_markdown(discord.utils.escape_mentions(text))


def _epn_embed(thread: _EpnThread) -> Any:
    """The announcement: the thread's title as a link to the thread (a 🔧 in front and an orange bar for a hotfix, a 📜 and a blue
    bar for anything else), the first lines of the post, and a footer in the same style as the Xbox status announcements. There is
    no heading above the title. Mentions in the forum's text are made harmless."""
    hotfix = bool(_EPN_HOTFIX.search(thread.title))
    teaser = _epn_safe(thread.teaser)[:4096] if thread.teaser else None  # (Discord's limits: 256 for the title, 4096 for the text)
    embed = discord.Embed(
        title=_epn_clean(("🔧 " if hotfix else "📜 ") + thread.title, 256),
        url=thread.url,
        description=teaser,
        colour=discord.Colour(_EPN_ORANGE if hotfix else _EPN_BLUE),
        timestamp=thread.posted,
    )
    embed.set_footer(text="Poss Bot watching [patch-notes]")
    return embed


# ----- the saved file ---------------------------------------------------------------------------------------------------

class _EpnStore:
    """The watcher's one small saved file. Knows nothing about Discord. It is saved atomically (a temporary file, then a swap),
    and a file that can't be read is moved aside, never overwritten."""

    def __init__(self, path: Path) -> None:
        self._path = path
        self._lock: Optional[asyncio.Lock] = None  # created on first use, inside the running event loop
        self._unsafe = False  # True if an unreadable file could not be moved aside

    def _set_aside(self, label: str) -> Optional[Path]:
        target = self._path.with_name(f"{self._path.name}.{label}-{_utcnow().strftime('%Y%m%dT%H%M%SZ')}")
        try:
            os.replace(self._path, target)
            return target
        except OSError:
            log.exception("Patch Notes watcher: could not set aside %s", self._path)
            return None

    def _unusable(self, error: BaseException) -> None:
        log.error("Patch Notes watcher: its saved file is unreadable (%s).", type(error).__name__)
        saved = self._set_aside("corrupt")
        if saved is None:
            self._unsafe = True  # refuse to write, so the damaged file can't be overwritten
            log.error("Patch Notes watcher: the unreadable file could not be moved aside, so nothing will be saved until it is fixed.")
        else:
            log.error("Patch Notes watcher: the unreadable file was kept as %s and the watcher starts from scratch.", saved.name)
        return None

    def load(self) -> Optional[Dict[str, Any]]:
        """{"category_id": number, "seen": [thread numbers]} from the saved file, or None if there is no usable file (the very
        first start, or a file that was unreadable and has been set aside)."""
        try:
            text = self._path.read_text(encoding="utf-8")
        except FileNotFoundError:
            return None
        except (OSError, ValueError) as error:
            return self._unusable(error)
        try:
            data = json.loads(text)
            if not isinstance(data, dict) or data.get("version") != 1:
                raise ValueError("not a version 1 file")
            seen = data["seen"]
            category = data.get("category_id", 0)
            if not isinstance(seen, list) or len(seen) > 5000 or isinstance(category, bool) or not isinstance(category, int) or category < 0:
                raise ValueError("unexpected contents")
        except (ValueError, KeyError, TypeError, RecursionError) as error:
            return self._unusable(error)
        return {"category_id": category, "seen": [_epn_int(value) for value in seen if _epn_int(value)]}

    def _write(self, text: str) -> None:
        self._path.parent.mkdir(parents=True, exist_ok=True)
        temp = self._path.with_name(self._path.name + ".tmp")
        try:
            with open(temp, "w", encoding="utf-8") as handle:
                handle.write(text)
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temp, self._path)  # all-or-nothing swap
        except OSError:
            with contextlib.suppress(OSError):
                os.remove(temp)
            raise

    async def save(self, snapshot: Dict[str, Any]) -> None:
        """Write the snapshot atomically. Raises OSError if the file can't be written."""
        if self._lock is None:
            self._lock = asyncio.Lock()
        async with self._lock:
            if self._unsafe:
                raise OSError("the saved file is unreadable and was not moved aside; refusing to overwrite it")
            await asyncio.get_running_loop().run_in_executor(None, self._write, json.dumps(snapshot, indent=2, sort_keys=True))


# ----- the watcher ---------------------------------------------------------------------------------------------------------

class _EpnWatcher:
    """Looks at the Patch Notes category every `interval` seconds and announces each new thread once. A failed or odd answer from the
    forum is logged (and, after a few in a row, reported to the owner); it is never announced."""

    def __init__(self, client: Any, interval: float, path: Path) -> None:
        self.bot = client
        self.interval = interval
        self.store = _EpnStore(path)
        self.category_id = 0  # the Patch Notes category's number, once known (the list of seen threads below belongs to it)
        self.refresh = False  # True: ask the forum for the category's number again at the next check
        self.seen: Optional[List[int]] = None  # numbers of the threads already dealt with; None until the first look
        self.fails = 0  # checks in a row that gave no usable answer
        self.warned_fail = False  # a warning about failing checks has been sent, so a "can be read again" is owed
        self.blocked = 0  # checks in a row where an announcement was due but could not be posted for want of a usable channel
        self.polling = False
        self.sent: List[float] = []  # when each recent announcement was posted
        self.tries: Dict[int, int] = {}  # how many times Discord has refused each thread's announcement
        self.warned: Dict[str, float] = {}  # when each kind of warning was last sent
        self.noted: Set[str] = set()  # things already logged, so each is logged once
        self.wait_until = 0.0  # no request before this moment (a Retry-After from the forum)
        self.problem = ""  # why the owner's channel can't be used, so each reason is logged once
        self.where = "the announcement channel"  # how messages to the owner name the place announcements go

    def _note(self, key: str, level: int, message: str, *args: Any) -> None:
        if key not in self.noted:
            self.noted.add(key)
            log.log(level, message, *args)

    # ----- start-up ---------------------------------------------------------

    def restore(self) -> None:
        """Pick up what the previous run saved. With no usable file the first look sets the starting point."""
        saved = self.store.load()
        if saved is None:
            log.info("Patch Notes watcher: no saved list of threads, so the first look sets the starting point.")
            return
        self.seen = list(saved["seen"])
        self.category_id = saved["category_id"]
        log.info("Patch Notes watcher: carrying on from the saved list (%d thread(s) already dealt with).", len(self.seen))

    async def check_destination(self) -> None:
        """Say in the log, once at start-up, where announcements will go."""
        mode, _, _ = _esom_target()
        channel, problem = await _esom_destination(self.bot, mode)
        if channel is None:
            log.warning("Patch Notes watcher: nothing can be announced right now: %s.", problem)
            return
        self.where = f"#{getattr(channel, 'name', '?')}"
        log.info("Patch Notes watcher: announcements go to #%s in “%s” (%s mode).", getattr(channel, "name", "?"), getattr(channel.guild, "name", "?"), mode)

    # ----- saving -----------------------------------------------------------

    async def _save(self, now: datetime) -> None:
        seen = sorted(self.seen or [], reverse=True)[:_EPN_SEEN_KEEP]
        snapshot = {"version": 1, "saved_at": _iso(now), "category_id": self.category_id, "seen": seen}
        try:
            await self.store.save(snapshot)
        except OSError as error:
            self._note("save", logging.ERROR, "Patch Notes watcher: could not save its list (%s). It keeps working, but a restart could repeat an announcement.", type(error).__name__)
        else:
            self.noted.discard("save")

    def _mark(self, ident: int) -> None:
        """Remember that this thread has been dealt with."""
        if self.seen is None:
            self.seen = []
        if ident not in self.seen:
            self.seen.append(ident)
        if len(self.seen) > _EPN_SEEN_KEEP:
            self.seen = sorted(self.seen, reverse=True)[:_EPN_SEEN_KEEP]

    # ----- messages to the owner ------------------------------------------------

    def _unusable(self, why: str) -> None:
        if why != self.problem:
            self.problem = why
            log.warning("Patch Notes watcher: not posting to the owner's channel, only to the log: %s", why)
        return None

    async def _owner_channel(self) -> Optional[Any]:
        """The channel for messages to the owner (the same test channel the ESO observer uses) if it can be used right now."""
        if not ESO_OBSERVER_CHANNEL_ID:
            return self._unusable("no channel is set (ESO_OBSERVER_CHANNEL_ID is 0)")
        channel = self.bot.get_channel(ESO_OBSERVER_CHANNEL_ID)
        if channel is None:
            try:
                channel = await self.bot.fetch_channel(ESO_OBSERVER_CHANNEL_ID)
            except discord.NotFound:
                return self._unusable("the channel no longer exists")
            except discord.Forbidden:
                return self._unusable("I don't have access to the channel")
            except discord.HTTPException:
                return self._unusable("Discord didn't answer when I looked the channel up")
        if not isinstance(channel, discord.TextChannel) or getattr(channel, "id", None) != ESO_OBSERVER_CHANNEL_ID:
            return self._unusable("it isn't a text channel")
        guild = channel.guild
        mod_log = self.bot.get_channel(MOD_LOG_CHANNEL_ID)
        if mod_log is not None and getattr(getattr(mod_log, "guild", None), "id", None) == getattr(guild, "id", None):
            return self._unusable("the channel is in the same server as the mod-log channel, so it is not the test server")
        me = getattr(guild, "me", None)
        if me is not None:  # (if the bot's own member isn't known yet, the send itself will show whether it is allowed)
            permissions = channel.permissions_for(me)
            if not (permissions.view_channel and permissions.send_messages):
                return self._unusable("I'm missing View Channel or Send Messages there")
        if self.problem:
            log.info("Patch Notes watcher: posting to the owner's channel again")
            self.problem = ""
        return channel

    async def _say(self, text: str, ping: bool = False) -> bool:
        """Post a message to the owner's channel, pinging ESO_OBSERVER_PING_USER_ID if `ping` (allowed to reach that member and
        nobody else). If the channel can't be used the text only goes to the log. True if it was posted."""
        text = text[:1900]
        who = _esom_id(ESO_OBSERVER_PING_USER_ID) if ping else 0  # (0 = nobody is pinged)
        channel = await self._owner_channel()
        if channel is None:
            log.info("Patch Notes watcher (not posted):\n%s", text)
            return False
        allowed = discord.AllowedMentions.none()
        if who:
            text = f"<@{who}> {text}"
            allowed = discord.AllowedMentions(everyone=False, roles=False, users=[discord.Object(id=who)], replied_user=False)
        try:
            await asyncio.wait_for(channel.send(text, allowed_mentions=allowed), _EPN_SEND_TIMEOUT)
        except asyncio.TimeoutError:
            log.warning("Patch Notes watcher: Discord took too long to accept a message to the owner's channel")
            return False
        except discord.HTTPException as error:
            log.warning("Patch Notes watcher: Discord refused a message to the owner's channel (HTTP %s)", getattr(error, "status", "?"))
            return False
        return True

    async def _warn(self, topic: str, text: str) -> bool:
        """A ⚠️ warning with a ping, at most once an hour for each topic."""
        now = _epn_mono()
        last = self.warned.get(topic)
        if last is not None and now - last < _EPN_WARN_EVERY:
            return False
        self.warned[topic] = now
        await self._say(text, ping=True)
        return True

    # ----- one check --------------------------------------------------------

    async def _lookup_category(self) -> int:
        """Ask the forum for its list of categories and return the number of the Patch Notes one."""
        names: List[str] = []
        for page in range(1, _EPN_CATEGORY_PAGES + 1):
            data = await _epn_fetch("/categories?" + urllib.parse.urlencode({"limit": 100, "page": page}))
            if not isinstance(data, list):
                raise _EpnError("the forum's list of categories was not a list", topic="shape")
            found, seen = _epn_pick_category(data)
            if found:
                log.info("Patch Notes watcher: the Patch Notes category is number %d.", found)
                return found
            fresh = [name for name in seen if name not in names]
            if not fresh:
                break  # an empty page, or only categories seen already: that was all of them
            names.extend(fresh)
        shown = _epn_safe(", ".join(names[:40])) or "none"
        if len(names) > 40:
            shown += f" … and {len(names) - 40} more"
        raise _EpnError(
            "no category called patch-notes was found",
            detail=f"I asked the forum for its list of categories but none of them is called patch-notes. The ones I saw: {shown}.",
            topic="category",
        )

    async def _category(self) -> int:
        configured = _esom_id(ESO_PATCH_NOTES_CATEGORY_ID)
        if configured:
            return configured
        if self.category_id and not self.refresh:
            return self.category_id
        found = await self._lookup_category()
        self.refresh = False
        return found

    async def _read(self) -> List[_EpnThread]:
        """The newest threads of the Patch Notes category. Raises _EpnError if the forum gave no trustworthy answer."""
        category = await self._category()
        if self.category_id and category != self.category_id:
            log.warning("Patch Notes watcher: the category is now number %d, not %d, so the saved list is dropped and a new starting point is taken.", category, self.category_id)
            self.seen = None
        self.category_id = category
        query = urllib.parse.urlencode({"categoryID": category, "limit": _EPN_LIST_LIMIT, "sort": "-dateInserted"})
        try:
            threads = _epn_threads(await _epn_fetch("/discussions?" + query))
        except _EpnError as error:
            if error.kind == "HTTP 404":
                self.refresh = True  # the number may have changed: ask the forum for the category again next time
            raise
        here = [thread for thread in threads if thread.category_id == category]
        if threads and not here:
            self.refresh = True
            raise _EpnError(
                "the forum answered with threads from other categories",
                detail="I asked for the threads of the Patch Notes category and got threads from other categories. If ESO_PATCH_NOTES_CATEGORY_ID is set in bot.py, check that it is the right number.",
                topic="category",
            )
        return here

    async def poll(self) -> None:
        if self.polling:  # a check is already running: never run two at once
            log.debug("Patch Notes watcher: a check is already running")
            return
        self.polling = True
        try:
            try:
                threads = await self._read()
            except _EpnError as error:
                await self._failed(error)
                return
            await self._recovered()
            await self._process(threads)
        finally:
            self.polling = False

    async def _failed(self, error: _EpnError) -> None:
        self.fails += 1
        if error.wait:
            self.wait_until = max(self.wait_until, _epn_mono() + error.wait)
        if self.fails == 1:
            log.warning("Patch Notes watcher: the check failed (%s). Nothing is announced from a failed check.", error.kind)
        elif self.fails % 30 == 0:
            log.warning("Patch Notes watcher: still failing after %d checks in a row (%s).", self.fails, error.kind)
        if self.fails < _EPN_FAILS_BEFORE_WARNING:
            return
        if error.topic == "category":
            title, body = "can't find the Patch Notes category", error.detail
            body += " To fix it, set ESO_PATCH_NOTES_CATEGORY_ID in bot.py to the number of the right category."
        elif error.topic == "shape":
            title = "the forum's answer looks different"
            body = f"{self.fails} checks in a row gave an answer I don't recognise ({error.kind}). The forum may have changed how it answers."
        else:
            title = "the ESO forum can't be read"
            body = f"{self.fails} checks in a row failed. Latest: **{error.kind}**."
        text = f"⚠️ **Patch Notes watcher · {title}** · {_eso_when(_epn_now())}\n{body}\nNew patch notes are not announced until this works."
        if await self._warn(error.topic, text):
            self.warned_fail = True

    async def _recovered(self) -> None:
        if not self.fails:
            return
        log.info("Patch Notes watcher: the forum can be read again after %d failed check(s).", self.fails)
        was_warned, count = self.warned_fail, self.fails
        self.fails, self.warned_fail = 0, False
        for topic in ("read", "category", "shape"):  # (a warning about posting is not ended by being able to read)
            self.warned.pop(topic, None)
        if was_warned:
            await self._say(f"✅ **Patch Notes watcher · the ESO forum can be read again** · {_eso_when(_epn_now())}\n{count} checks in a row had failed.")

    async def _process(self, threads: List[_EpnThread]) -> None:
        now = _epn_now()
        ordered = sorted(threads, key=lambda thread: (thread.posted.timestamp() if thread.posted is not None else 0.0, thread.ident))
        if self.seen is None:
            await self._first_look(ordered, now)
            return
        known = set(self.seen)
        skipped = False
        announced = 0
        for thread in ordered:
            if thread.ident in known:
                continue
            if thread.posted is not None and (now - thread.posted).total_seconds() > _EPN_MAX_AGE:
                log.info("Patch Notes watcher: not announcing “%s” (thread %d): it was posted more than a week ago.", thread.title, thread.ident)
                self._mark(thread.ident)
                skipped = True
                continue
            if announced >= _EPN_MAX_PER_RUN:
                log.warning("Patch Notes watcher: more than %d new threads at once; the rest are announced at the next checks.", _EPN_MAX_PER_RUN)
                break
            outcome = await self._announce(thread)
            if outcome == "later":
                break  # keep the order: nothing newer goes out before this one
            await self._save(now)  # remembered at once, so nothing that goes wrong later can make a restart announce it again
            skipped = False  # (that save included any thread skipped before it)
            announced += outcome == "sent"
        if skipped:
            await self._save(now)

    async def _first_look(self, ordered: List[_EpnThread], now: datetime) -> None:
        """The very first look: every thread already there is taken as seen, except the newest one if it is young enough to
        be announced (see ESO_PATCH_NOTES_FIRST_RUN_HOURS). Then the owner is told what was found."""
        newest = ordered[-1] if ordered else None
        self.seen = [thread.ident for thread in ordered]
        pending: Optional[_EpnThread] = None
        window = _epn_first_run_seconds()
        if newest is not None and window and newest.posted is not None and -300 <= (now - newest.posted).total_seconds() <= window:
            pending = newest
            self.seen.remove(newest.ident)
        await self._save(now)  # the starting point is saved before anything is posted
        log.info("Patch Notes watcher: the starting point is set (%d thread(s) already there; nothing older is announced).", len(ordered))
        outcome = ""
        if pending is not None:
            log.info("Patch Notes watcher: the newest thread, “%s”, is under %d hours old, so it is announced now.", pending.title, int(window // 3600))
            outcome = await self._announce(pending)
            if outcome != "later":
                await self._save(now)
        await self._say_first_look(ordered, pending, outcome)

    async def _say_first_look(self, ordered: List[_EpnThread], pending: Optional[_EpnThread], outcome: str) -> None:
        newest = ordered[-1] if ordered else None
        lines = [
            f"🔎 **Patch Notes watcher · first look** · {_eso_when(_epn_now())}",
            f"I can read the ESO forum. The Patch Notes category is number {self.category_id}, and I looked at its newest {len(ordered)} thread(s).",
        ]
        if newest is not None:
            when = f" (posted {_eso_when(newest.posted)})" if newest.posted is not None else ""
            lines.append(f"Newest thread: “{_epn_safe(newest.title)}”{when}.")
            lines.append(f"<{newest.url}>")
        if pending is not None and outcome == "sent":
            lines.append(f"I announced that thread in {self.where}, because it is less than {int(_epn_first_run_seconds() // 3600)} hours old.")
        elif pending is not None and outcome == "later":
            lines.append("I could not announce that thread yet (see the log); I will try again at the next check.")
        elif pending is not None:
            lines.append("Discord refused that thread's announcement, so it was skipped.")
        else:
            lines.append(f"Nothing was announced. From now on, each new thread there is announced in {self.where}.")
        await self._say("\n".join(lines))

    # ----- announcing -------------------------------------------------------

    async def _announce(self, thread: _EpnThread) -> str:
        """Post one thread in the one allowed channel. "sent": posted. "gave up": Discord refused it too many times, so it is
        skipped for good. "later": it could not be posted now and is tried again at the next check."""
        now = _epn_mono()
        self.sent = [moment for moment in self.sent if now - moment < 3600]
        if len(self.sent) >= _EPN_MAX_PER_HOUR:
            self._note(
                "hour", logging.WARNING,
                "Patch Notes watcher: holding back “%s”: %d announcements were already made in the last hour; it is announced when the hour allows.",
                thread.title, _EPN_MAX_PER_HOUR,
            )
            return "later"
        self.noted.discard("hour")
        mode, _, _ = _esom_target()
        channel, problem = await _esom_destination(self.bot, mode)
        if channel is None:
            self._note("dest:" + problem, logging.WARNING, "Patch Notes watcher: not announcing “%s” yet: %s.", thread.title, problem)
            self.blocked += 1
            if self.blocked >= _EPN_FAILS_BEFORE_WARNING:
                await self._warn("destination", "\n".join([
                    f"⚠️ **Patch Notes watcher · I can't post announcements** · {_eso_when(_epn_now())}",
                    f"A new thread is waiting, but I can't use the announcement channel: {problem}.",
                    "It is announced as soon as that is fixed.",
                ]))
            return "later"
        self.blocked = 0
        self.noted = {key for key in self.noted if not key.startswith("dest:")}
        refused = ""
        try:
            await asyncio.wait_for(channel.send(embed=_epn_embed(thread), allowed_mentions=discord.AllowedMentions.none()), _EPN_SEND_TIMEOUT)
        except asyncio.TimeoutError:
            refused = "Discord took too long to accept it"
        except discord.HTTPException as error:
            refused = f"Discord refused it (HTTP {getattr(error, 'status', '?')})"
        if not refused:
            self.sent.append(now)
            self._mark(thread.ident)
            self.tries.pop(thread.ident, None)
            log.info("Patch Notes watcher: announced “%s” (thread %d).", thread.title, thread.ident)
            return "sent"
        self.tries[thread.ident] = self.tries.get(thread.ident, 0) + 1
        if self.tries[thread.ident] < _EPN_SEND_TRIES:
            log.error("Patch Notes watcher: could not announce “%s” (thread %d): %s. It is tried again at the next check.", thread.title, thread.ident, refused)
            return "later"
        log.error("Patch Notes watcher: giving up on announcing “%s” (thread %d): %s, %d times.", thread.title, thread.ident, refused, _EPN_SEND_TRIES)
        self._mark(thread.ident)
        self.tries.pop(thread.ident, None)
        await self._warn(f"gave up {thread.ident}", "\n".join([
            f"⚠️ **Patch Notes watcher · I couldn't post a thread** · {_eso_when(_epn_now())}",
            f"“{_epn_safe(thread.title)}” could not be announced: {refused}, {_EPN_SEND_TRIES} times. It is skipped.",
            f"<{thread.url}>",
        ]))
        return "gave up"

    # ----- the loop ---------------------------------------------------------

    def delay(self) -> float:
        """Seconds until the next check: the interval, doubling while checks keep failing (up to a limit), and never sooner than a
        wait the forum asked for."""
        if self.fails <= 1:
            base = self.interval
        else:
            base = min(self.interval * 2 ** min(self.fails - 1, 20), max(self.interval, _EPN_BACKOFF_CAP))  # (20: far past the limit, but no overflow)
        return max(base, self.wait_until - _epn_mono())

    async def _sleep(self, seconds: float) -> None:
        """Sleep in short slices so the watcher notices at once that the bot is shutting down."""
        end = _epn_mono() + seconds
        while not self.bot.is_closed():
            left = end - _epn_mono()
            if left <= 0:
                return
            await asyncio.sleep(min(left, _EPN_SLEEP_SLICE))

    async def run(self) -> None:
        try:
            await self.bot.wait_until_ready()
            log.info("Patch Notes watcher started: checking the ESO forum every %s seconds.", self.interval)
            try:
                self.restore()
            except Exception:
                log.exception("Patch Notes watcher: its saved list could not be used; the first look sets a new starting point")
                self.seen, self.category_id = None, 0
            try:
                await self.check_destination()
            except asyncio.CancelledError:
                raise
            except Exception:
                log.exception("Patch Notes watcher: could not check where announcements will go")
            while not self.bot.is_closed():
                try:
                    await self.poll()
                except asyncio.CancelledError:
                    raise
                except Exception:
                    log.exception("Patch Notes watcher: unexpected error (it keeps going)")
                await self._sleep(self.delay())
        except asyncio.CancelledError:
            raise
        except Exception:
            log.exception("Patch Notes watcher stopped because of an unexpected error")
        finally:
            log.info("Patch Notes watcher stopped")


_epn_task: Optional[asyncio.Task] = None


@bot.listen("on_ready")
async def eso_patch_notes_ready():
    """Start the watcher once. on_ready fires again after every reconnect, so a watcher that is already running is kept."""
    global _epn_task
    try:
        if not _EPN_ENABLED:
            log.info("Patch Notes watcher is switched off (the ESO_PATCH_NOTES setting is off).")
        elif _epn_task is None or _epn_task.done():
            problem = _esom_config_problem()
            if problem:
                log.warning("Patch Notes watcher is off, and nothing will be announced anywhere: %s.", problem)
            else:
                _epn_task = asyncio.create_task(_EpnWatcher(bot, _EPN_INTERVAL, _EPN_STATE_FILE).run(), name="eso-patch-notes")
    except Exception:
        log.exception("The Patch Notes watcher could not be started")


# --------------------------------------------------------------------------
# Error handling
# --------------------------------------------------------------------------


@bot.tree.error
async def on_app_command_error(interaction: discord.Interaction, error: app_commands.AppCommandError):
    if isinstance(error, app_commands.MissingPermissions):
        message = "You don't have permission to use this command."
    elif isinstance(error, app_commands.NoPrivateMessage):
        message = "This command can only be used in a server."
    else:
        log.error("Unhandled app command error", exc_info=error)
        message = "Something went wrong running that command."

    if interaction.response.is_done():
        await interaction.followup.send(message, ephemeral=True)
    else:
        await interaction.response.send_message(message, ephemeral=True)


if __name__ == "__main__":
    bot.run(TOKEN)
