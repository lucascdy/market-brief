#!/usr/bin/env python3
"""Brief quotidien des marchés financiers et de la macro (mode matin ou soir).

Usage:
    python brief.py matin
    python brief.py soir

Produit 3 fichiers datés dans briefs/ :
- YYYY-MM-DD-{mode}-resume.html   -> petit résumé, ouvert automatiquement à l'écran
- YYYY-MM-DD-{mode}-complet.html  -> rapport détaillé, lié depuis le résumé
- YYYY-MM-DD-{mode}.md            -> archive texte pour l'historique

Le script détecte aussi les marchés probablement fermés (clôture ancienne),
signale si plusieurs sources de données sont indisponibles simultanément
(brief potentiellement dégradé), et purge automatiquement l'historique au-delà
de --keep-days jours.

Sources gratuites, sans clé API :
- Indices, devises, volatilité & matières premières : Yahoo Finance (via yfinance)
- Taux directeurs / obligataires : FRED (Federal Reserve Bank of St. Louis), CSV public
- Calendrier économique : ForexFactory (flux JSON public de la semaine)
- Actus macro/marchés : Google News RSS (agrège Les Echos, Reuters, Bloomberg, etc.)
"""

from __future__ import annotations

import argparse
import csv
import html
import json
import logging
import os
import re
import smtplib
import subprocess
import sys
from datetime import date, datetime
from email.message import EmailMessage
from pathlib import Path
from urllib.parse import quote_plus
from zoneinfo import ZoneInfo

import feedparser
import requests
import yfinance as yf
from dateutil import parser as dateutil_parser

PARIS_TZ = ZoneInfo("Europe/Paris")

# --------------------------------------------------------------------------
# Configuration des sources
# --------------------------------------------------------------------------

ALL_INDICES = {
    "Nikkei 225": "^N225",
    "CAC 40": "^FCHI",
    "Eurostoxx 50": "^STOXX50E",
    "S&P 500": "^GSPC",
    "Nasdaq": "^IXIC",
}
INDICES_MATIN = ["Nikkei 225", "S&P 500", "Nasdaq"]
INDICES_SOIR = ["CAC 40", "Eurostoxx 50", "S&P 500", "Nasdaq"]

EXTRA_ASSETS = {
    "VIX (volatilité)": "^VIX",
    "Or (once, USD)": "GC=F",
    "Pétrole WTI": "CL=F",
    "Pétrole Brent": "BZ=F",
}
EXTRA_ASSETS_SUMMARY = ["VIX (volatilité)", "Or (once, USD)", "Pétrole WTI"]

FX = {"EUR/USD": "EURUSD=X"}

# Seuils de variation % jour à partir desquels un mouvement est jugé "notable"
BIG_MOVE_THRESHOLDS = {
    **{name: 1.5 for name in ALL_INDICES},
    **{name: 1.0 for name in FX},
    "VIX (volatilité)": 10.0,
    "Or (once, USD)": 2.5,
    "Pétrole WTI": 3.0,
    "Pétrole Brent": 3.0,
}
VIX_FEAR_LEVEL = 25.0
DEFAULT_WATCHLIST_MOVE_THRESHOLD = 3.0

RATE_SERIES_FULL = {
    "BCE — taux de refinancement": "ECBMRRFR",
    "BCE — facilité de dépôt": "ECBDFR",
    "Fed — borne basse (target range)": "DFEDTARL",
    "Fed — borne haute (target range)": "DFEDTARU",
    "10 ans US (Treasury)": "DGS10",
    "10 ans France (OAT, dernier point mensuel)": "IRLTLT01FRM156N",
}
RATE_LABELS_SUMMARY = [
    "BCE — facilité de dépôt",
    "Fed — borne haute (target range)",
    "10 ans US (Treasury)",
    "10 ans France (OAT, dernier point mensuel)",
]

DEFAULT_NEWS_QUERY = (
    '(bourse OR "marchés financiers" OR macroéconomie OR banque centrale) '
    "(site:lesechos.fr OR site:reuters.com OR site:bloomberg.com OR site:boursorama.com)"
)
NEWS_ITEMS_FULL = 10
NEWS_ITEMS_SUMMARY = 5

CALENDAR_URL = "https://nfs.faireconomy.media/ff_calendar_thisweek.json"
CALENDAR_CURRENCIES = {"USD", "EUR"}
CALENDAR_IMPACTS = {"High", "Medium"}
CALENDAR_ITEMS_FULL = 15

MOIS_FR = [
    "janvier", "février", "mars", "avril", "mai", "juin",
    "juillet", "août", "septembre", "octobre", "novembre", "décembre",
]
JOURS_FR = ["lundi", "mardi", "mercredi", "jeudi", "vendredi", "samedi", "dimanche"]

BRIEF_FILE_RE = re.compile(r"^(\d{4}-\d{2}-\d{2})-")


# --------------------------------------------------------------------------
# Récupération des données (chaque source échoue indépendamment des autres)
# --------------------------------------------------------------------------

def fetch_index(name: str, symbol: str) -> dict | None:
    """Niveau + variation vs veille, vs 5 séances, et depuis le 1er janvier, via Yahoo Finance.

    Un seul appel réseau (period="ytd") sert à la fois l'historique court affiché
    (5 dernières séances) et le calcul de performance depuis le début de l'année.
    """
    try:
        hist = yf.Ticker(symbol).history(period="ytd")
        closes = hist["Close"].dropna()
        if len(closes) < 2:
            raise ValueError("historique insuffisant")
        full_history = [(idx.date(), float(v)) for idx, v in closes.items()]
        recent = full_history[-5:]
        last, prev, first_recent = recent[-1][1], recent[-2][1], recent[0][1]
        ytd_first = full_history[0][1]
        return {
            "level": last,
            "change_pct": (last - prev) / prev * 100,
            "change_5d_pct": (last - first_recent) / first_recent * 100,
            "history_span": len(recent) - 1,
            "history": recent,
            "ytd_change_pct": (last - ytd_first) / ytd_first * 100,
        }
    except Exception as exc:
        logging.warning("[%s] indisponible (Yahoo Finance) : %s", name, exc)
        return None


def fetch_indices(tickers: dict[str, str]) -> dict[str, dict | None]:
    return {name: fetch_index(name, symbol) for name, symbol in tickers.items()}


def mark_staleness(indices: dict[str, dict | None], mode: str, today: date) -> None:
    """Signale une clôture qui n'est pas celle attendue (marché probablement fermé)."""
    for info in indices.values():
        if info is None:
            continue
        last_date = info["history"][-1][0]
        if mode == "soir":
            info["stale"] = last_date != today
        else:
            info["stale"] = (today - last_date).days > 3


def fetch_fred_latest(series_id: str) -> tuple[str, float] | None:
    """Dernière valeur non manquante d'une série FRED, via l'export CSV public (sans clé)."""
    url = f"https://fred.stlouisfed.org/graph/fredgraph.csv?id={series_id}"
    try:
        resp = requests.get(url, timeout=10)
        resp.raise_for_status()
        rows = list(csv.DictReader(resp.text.splitlines()))
        valid = [r for r in rows if r.get(series_id) not in (".", "", None)]
        if not valid:
            raise ValueError("aucune donnée valide dans la série")
        last = valid[-1]
        return last["observation_date"], float(last[series_id])
    except Exception as exc:
        logging.warning("[FRED %s] indisponible : %s", series_id, exc)
        return None


def fetch_rates() -> dict[str, tuple[str, float] | None]:
    return {label: fetch_fred_latest(series_id) for label, series_id in RATE_SERIES_FULL.items()}


def fetch_news(query: str, max_items: int) -> list[dict]:
    """Actus macro/marchés via Google News RSS (gratuit, sans clé)."""
    url = f"https://news.google.com/rss/search?q={quote_plus(query)}&hl=fr&gl=FR&ceid=FR:fr"
    try:
        # Récupéré via `requests` (certifi) plutôt que l'ouverture réseau interne de
        # feedparser, qui peut échouer sur les certificats CA du système.
        resp = requests.get(url, timeout=10, headers={"User-Agent": "Mozilla/5.0"})
        resp.raise_for_status()
        feed = feedparser.parse(resp.content)
        if not feed.entries:
            raise ValueError(getattr(feed, "bozo_exception", "flux vide"))
        return [{"title": e.title, "link": e.link} for e in feed.entries[:max_items]]
    except Exception as exc:
        logging.warning("Actus indisponibles (Google News) : %s", exc)
        return []


def fetch_calendar_week() -> list[dict]:
    """Évènements macro de la semaine (USD/EUR, impact moyen ou élevé), via ForexFactory."""
    try:
        resp = requests.get(CALENDAR_URL, timeout=10, headers={"User-Agent": "Mozilla/5.0"})
        resp.raise_for_status()
        events = resp.json()
    except Exception as exc:
        logging.warning("Calendrier économique indisponible (ForexFactory) : %s", exc)
        return []

    result = []
    for ev in events:
        try:
            ev_dt = dateutil_parser.isoparse(ev["date"])
        except Exception:
            continue
        if ev.get("country") not in CALENDAR_CURRENCIES:
            continue
        if ev.get("impact") not in CALENDAR_IMPACTS:
            continue
        result.append({**ev, "_dt": ev_dt.astimezone(PARIS_TZ)})

    result.sort(key=lambda e: e["_dt"])
    return result


def events_on(events: list[dict], target_date: date) -> list[dict]:
    return [ev for ev in events if ev["_dt"].date() == target_date]


def load_watchlist(path: Path) -> dict[str, str]:
    """Charge {nom: symbole} depuis un watchlist.json optionnel ({"tickers": {...}})."""
    if not path.exists():
        return {}
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
        tickers = raw.get("tickers", {})
        if not isinstance(tickers, dict):
            raise ValueError("'tickers' doit être un objet {nom: symbole}")
        return {str(k): str(v) for k, v in tickers.items()}
    except Exception as exc:
        logging.warning("Watchlist indisponible (%s) : %s", path, exc)
        return {}


# --------------------------------------------------------------------------
# Mouvements de marché notables
# --------------------------------------------------------------------------

def compute_big_moves(data: dict) -> list[str]:
    """Instruments dont la variation du jour dépasse un seuil jugé notable."""
    moves = []
    instruments = {**data["indices"], **data["extra"], **data["fx"], **data.get("watchlist", {})}
    for name, info in instruments.items():
        if info is None:
            continue
        threshold = BIG_MOVE_THRESHOLDS.get(name, DEFAULT_WATCHLIST_MOVE_THRESHOLD)
        if abs(info["change_pct"]) >= threshold:
            moves.append(f"{name} {fmt_pct(info['change_pct'])}")

    vix = data["extra"].get("VIX (volatilité)")
    if vix and vix["level"] >= VIX_FEAR_LEVEL and not any("VIX" in m for m in moves):
        moves.append(f"VIX à {fmt_level(vix['level'])} (niveau de stress élevé)")

    return moves


# --------------------------------------------------------------------------
# Santé des données (détecte une panne large de plusieurs sources à la fois)
# --------------------------------------------------------------------------

def compute_health(data: dict) -> dict:
    instruments = {**data["indices"], **data["extra"], **data["fx"]}
    total_instr = len(instruments)
    ok_instr = sum(1 for v in instruments.values() if v is not None)
    instr_ratio = ok_instr / total_instr if total_instr else 1.0

    total_rates = len(data["rates"])
    ok_rates = sum(1 for v in data["rates"].values() if v is not None)
    rates_ratio = ok_rates / total_rates if total_rates else 1.0

    news_ok = bool(data["news"])
    calendar_ok = bool(data["calendar_week"])

    failing = []
    if instr_ratio < 0.5:
        failing.append("indices/devises/matières premières")
    if rates_ratio < 0.5:
        failing.append("taux")
    if not news_ok:
        failing.append("actus")
    if not calendar_ok:
        failing.append("calendrier économique")

    return {
        "instr_ratio": instr_ratio,
        "rates_ratio": rates_ratio,
        "news_ok": news_ok,
        "calendar_ok": calendar_ok,
        "failing_categories": failing,
        "degraded": len(failing) >= 2,
    }


# --------------------------------------------------------------------------
# Mise en forme (valeurs)
# --------------------------------------------------------------------------

def format_date_fr(d: date) -> str:
    return f"{JOURS_FR[d.weekday()]} {d.day} {MOIS_FR[d.month - 1]} {d.year}"


def fmt_level(value: float) -> str:
    return f"{value:,.2f}".replace(",", " ")


def fmt_pct(value: float) -> str:
    sign = "+" if value >= 0 else ""
    return f"{sign}{value:.2f} %"


def stale_suffix_html(info: dict) -> str:
    if not info.get("stale"):
        return ""
    last = info["history"][-1][0]
    return f' <span class="muted">— clôture du {last.strftime("%d/%m")}, marché probablement fermé</span>'


def stale_suffix_md(info: dict) -> str:
    if not info.get("stale"):
        return ""
    last = info["history"][-1][0]
    return f" (clôture du {last.strftime('%d/%m')}, marché probablement fermé)"


# --------------------------------------------------------------------------
# Mise en forme (texte brut, pour l'archive .md)
# --------------------------------------------------------------------------

def md_index_line(name: str, info: dict | None) -> str:
    if info is None:
        return f"- {name} : indisponible"
    return f"- {name} : {fmt_level(info['level'])} ({fmt_pct(info['change_pct'])}){stale_suffix_md(info)}"


def md_fx_line(name: str, info: dict | None) -> str:
    if info is None:
        return f"- {name} : indisponible"
    return f"- {name} : {info['level']:.4f} ({fmt_pct(info['change_pct'])})"


def md_rates_block(rates: dict[str, tuple[str, float] | None], labels: list[str]) -> str:
    lines = []
    for label in labels:
        data = rates.get(label)
        if data is None:
            lines.append(f"- {label} : indisponible")
        else:
            rate_date, value = data
            lines.append(f"- {label} : {value:.2f} % (au {rate_date})")
    return "\n".join(lines)


def md_news_block(items: list[dict]) -> str:
    if not items:
        return "_Actus indisponibles pour le moment (source injoignable)._"
    return "\n".join(f"{i}. {item['title']}" for i, item in enumerate(items, start=1))


def md_calendar_block(events: list[dict]) -> str:
    if not events:
        return "_Aucun évènement macro majeur EUR/USD identifié (ou source indisponible)._"
    lines = []
    for ev in events:
        heure = ev["_dt"].strftime("%Hh%M")
        lines.append(f"- {heure} — {ev.get('country', '')} — {ev.get('title', '')} (impact {ev.get('impact', '')})")
    return "\n".join(lines)


def build_markdown(data: dict) -> str:
    mode, today = data["mode"], data["today"]
    indices_subset = INDICES_MATIN if mode == "matin" else INDICES_SOIR
    indices_lines = "\n".join(md_index_line(name, data["indices"][name]) for name in indices_subset)
    extra_lines = "\n".join(md_index_line(name, data["extra"][name]) for name in EXTRA_ASSETS_SUMMARY)
    section_title = "Nuit dernière (Asie / clôture US)" if mode == "matin" else "Clôture du jour (Europe / US)"
    calendar_title = "À surveiller aujourd'hui en Europe" if mode == "matin" else "Demain au calendrier économique"
    mode_label = "Matin" if mode == "matin" else "Soir"

    alerts = []
    if data["health"]["degraded"]:
        hint = ""
        if "indices/devises/matières premières" in data["health"]["failing_categories"]:
            hint = " Cause fréquente : mettez à jour yfinance (`pip install --upgrade yfinance`)."
        alerts.append(
            f"**Attention** : sources indisponibles aujourd'hui ({', '.join(data['health']['failing_categories'])}) "
            f"— brief possiblement incomplet.{hint}"
        )
    if data["market_closed"]:
        alerts.append("**Info** : clôtures affichées anciennes — marché probablement fermé aujourd'hui.")
    if data.get("big_moves"):
        alerts.append(f"**Mouvement notable** : {' · '.join(data['big_moves'])}.")
    alert_block = ("\n".join(alerts) + "\n\n") if alerts else ""

    watchlist_section = ""
    if data.get("watchlist"):
        watchlist_lines = "\n".join(md_index_line(name, info) for name, info in data["watchlist"].items())
        watchlist_section = f"\n## Ma watchlist\n{watchlist_lines}\n"

    return f"""# Brief Marchés — {mode_label} — {format_date_fr(today)}

{alert_block}## {section_title}
{indices_lines}

## Volatilité & matières premières
{extra_lines}
{watchlist_section}
## Taux & devises
{md_rates_block(data["rates"], RATE_LABELS_SUMMARY)}
{md_fx_line("EUR/USD", data["fx"].get("EUR/USD"))}

## {calendar_title}
{md_calendar_block(data["calendar_target"])}

## Actus macro / marchés
{md_news_block(data["news"][:NEWS_ITEMS_SUMMARY])}

---
_Généré le {data["generated_at"]} (Europe/Paris). Sources : Yahoo Finance, FRED (Fed de St. Louis), ForexFactory, Google News. Données indicatives, non temps réel._
"""


# --------------------------------------------------------------------------
# Mise en forme (HTML)
# --------------------------------------------------------------------------

BASE_CSS = """
:root{color-scheme: light dark;}
*{box-sizing:border-box;}
body{font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Helvetica,Arial,sans-serif;
  max-width:720px;margin:40px auto;padding:0 20px;line-height:1.5;color:#1a1a1a;background:#fafafa;}
h1{font-size:1.5rem;margin:0 0 4px;}
h2{font-size:1.05rem;margin:0 0 10px;}
h3{font-size:.95rem;margin:16px 0 6px;}
.badge{display:inline-block;padding:2px 10px;border-radius:999px;background:#1a1a2e;color:#fff;
  font-size:.75rem;letter-spacing:.05em;text-transform:uppercase;}
.subtitle{color:#666;font-size:.9rem;margin:4px 0 20px;}
.card{background:#fff;border:1px solid #e5e5e5;border-radius:10px;padding:16px 20px;margin:16px 0;}
.row{display:flex;justify-content:space-between;gap:12px;padding:6px 0;border-bottom:1px solid #f0f0f0;}
.row:last-child{border-bottom:none;}
.up{color:#0a7d3c;font-weight:600;}
.down{color:#c0392b;font-weight:600;}
.muted{color:#888;font-size:.85rem;}
ul{margin:0;padding-left:1.2em;}
li{margin-bottom:8px;}
a{color:#1a56db;}
.cta{display:inline-block;margin-top:8px;padding:10px 18px;background:#1a1a2e;color:#fff !important;
  text-decoration:none;border-radius:8px;font-weight:600;font-size:.9rem;}
.back{display:inline-block;margin-bottom:16px;font-size:.85rem;}
footer{color:#999;font-size:.75rem;margin-top:24px;}
table{width:100%;border-collapse:collapse;font-size:.82rem;margin-bottom:8px;}
td,th{padding:3px 6px;text-align:right;border-bottom:1px solid #f0f0f0;}
td:first-child,th:first-child{text-align:left;}
.hist-grid{display:grid;grid-template-columns:1fr 1fr;gap:16px 24px;}
.sparkline{display:block;margin:2px 0 6px;}
code{background:rgba(127,127,127,.18);padding:1px 5px;border-radius:4px;
  font-family:ui-monospace,SFMono-Regular,Menlo,monospace;font-size:.85em;}
.alert{background:#fdecea;border:1px solid #c0392b;color:#8a1f11;padding:12px 16px;border-radius:8px;
  margin-bottom:16px;font-size:.85rem;}
.info-banner{background:#eaf2fd;border:1px solid #1a56db;color:#0d3a91;padding:12px 16px;border-radius:8px;
  margin-bottom:16px;font-size:.85rem;}
.move-banner{background:#fff4e0;border:1px solid #d97a06;color:#7a4a00;padding:12px 16px;border-radius:8px;
  margin-bottom:16px;font-size:.85rem;}
@media (max-width:480px){.hist-grid{grid-template-columns:1fr;}}
@media (prefers-color-scheme:dark){
  body{background:#111214;color:#eee;}
  .card{background:#1b1c1f;border-color:#2a2b2e;}
  .row,td,th{border-color:#2a2b2e;}
  .muted,footer{color:#999;}
  a{color:#7aa2ff;}
  .alert{background:#3a1a1a;border-color:#c0392b;color:#ffb4b4;}
  .info-banner{background:#132743;border-color:#3f7ce0;color:#bcd4fb;}
  .move-banner{background:#3a2a10;border-color:#d97a06;color:#ffd08a;}
}
"""


def html_page(title: str, body: str) -> str:
    return f"""<!doctype html>
<html lang="fr">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(title)}</title>
<style>{BASE_CSS}</style>
</head>
<body>
{body}
</body>
</html>
"""


def html_banners(data: dict) -> str:
    parts = []
    if data["health"]["degraded"]:
        cats = ", ".join(data["health"]["failing_categories"])
        hint = ""
        if "indices/devises/matières premières" in data["health"]["failing_categories"]:
            hint = (
                ' <span class="muted">Cause fréquente : la librairie <code>yfinance</code> désynchronisée '
                "avec Yahoo Finance — essayez <code>pip install --upgrade yfinance</code>.</span>"
            )
        parts.append(
            f'<div class="alert">⚠ Sources indisponibles aujourd\'hui : {html.escape(cats)}. '
            f"Le brief peut être incomplet.{hint}</div>"
        )
    if data["market_closed"]:
        parts.append(
            '<div class="info-banner">ℹ Clôtures affichées anciennes pour les indices ci-dessous — '
            "marché probablement fermé aujourd'hui (jour férié ou week-end).</div>"
        )
    if data.get("big_moves"):
        moves_str = " · ".join(data["big_moves"][:6])
        parts.append(f'<div class="move-banner">📈 Mouvement de marché notable : {html.escape(moves_str)}</div>')
    return "".join(parts)


def html_index_rows(
    names: list[str], indices: dict[str, dict | None], show_5d: bool = False, show_ytd: bool = False
) -> str:
    rows = []
    for name in names:
        info = indices.get(name)
        if info is None:
            rows.append(f'<div class="row"><span>{html.escape(name)}</span><span class="muted">indisponible</span></div>')
            continue
        css = "up" if info["change_pct"] >= 0 else "down"
        arrow = "▲" if info["change_pct"] >= 0 else "▼"
        extras = []
        if show_5d and info.get("history_span", 0) >= 2:
            css5 = "up" if info["change_5d_pct"] >= 0 else "down"
            extras.append(f'{info["history_span"]}j <span class="{css5}">{fmt_pct(info["change_5d_pct"])}</span>')
        if show_ytd and info.get("ytd_change_pct") is not None:
            cssy = "up" if info["ytd_change_pct"] >= 0 else "down"
            extras.append(f'YTD <span class="{cssy}">{fmt_pct(info["ytd_change_pct"])}</span>')
        extra_html = f' <span class="muted">· {" · ".join(extras)}</span>' if extras else ""
        rows.append(
            f'<div class="row"><span>{html.escape(name)}</span>'
            f'<span>{fmt_level(info["level"])} <span class="{css}">{arrow} {fmt_pct(info["change_pct"])}</span>'
            f'{extra_html}{stale_suffix_html(info)}</span></div>'
        )
    return "\n".join(rows)


def sparkline_svg(history: list[tuple[date, float]], width: int = 120, height: int = 32) -> str:
    if len(history) < 2:
        return ""
    values = [v for _, v in history]
    lo, hi = min(values), max(values)
    span = (hi - lo) or 1.0
    step = width / (len(values) - 1)
    points = " ".join(
        f"{i * step:.1f},{height - ((v - lo) / span) * height:.1f}" for i, v in enumerate(values)
    )
    color = "#0a7d3c" if values[-1] >= values[0] else "#c0392b"
    return (
        f'<svg viewBox="0 0 {width} {height}" width="{width}" height="{height}" class="sparkline" '
        f'preserveAspectRatio="none"><polyline points="{points}" fill="none" stroke="{color}" '
        f'stroke-width="2" stroke-linejoin="round" stroke-linecap="round"/></svg>'
    )


def html_index_history_tables(names: list[str], instruments: dict[str, dict | None]) -> str:
    blocks = []
    for name in names:
        info = instruments.get(name)
        if info is None or not info.get("history"):
            blocks.append(f"<div><h3>{html.escape(name)}</h3><p class='muted'>indisponible</p></div>")
            continue
        rows = "".join(f"<tr><td>{d.strftime('%d/%m')}</td><td>{fmt_level(v)}</td></tr>" for d, v in info["history"])
        blocks.append(
            f"<div><h3>{html.escape(name)}</h3>{sparkline_svg(info['history'])}"
            f"<table><tr><th>Date</th><th>Clôture</th></tr>{rows}</table></div>"
        )
    return f'<div class="hist-grid">{"".join(blocks)}</div>'


def html_rates_rows(rates: dict[str, tuple[str, float] | None], labels: list[str]) -> str:
    rows = []
    for label in labels:
        data = rates.get(label)
        if data is None:
            rows.append(f'<div class="row"><span>{html.escape(label)}</span><span class="muted">indisponible</span></div>')
        else:
            d, v = data
            rows.append(f'<div class="row"><span>{html.escape(label)}</span><span>{v:.2f} % <span class="muted">(au {d})</span></span></div>')
    return "\n".join(rows)


def html_news_list(items: list[dict]) -> str:
    if not items:
        return "<p class='muted'>Actus indisponibles pour le moment (source injoignable).</p>"
    lis = "".join(
        f'<li><a href="{html.escape(item["link"])}" target="_blank" rel="noopener">{html.escape(item["title"])}</a></li>'
        for item in items
    )
    return f"<ul>{lis}</ul>"


def html_calendar_list(events: list[dict]) -> str:
    if not events:
        return "<p class='muted'>Aucun évènement macro majeur identifié (ou source indisponible).</p>"
    lis = []
    for ev in events:
        heure = ev["_dt"].strftime("%a %d/%m %Hh%M")
        lis.append(
            f"<li>{html.escape(heure)} — {html.escape(ev.get('country', ''))} — "
            f"{html.escape(ev.get('title', ''))} <span class='muted'>(impact {html.escape(ev.get('impact', ''))})</span></li>"
        )
    return f"<ul>{''.join(lis)}</ul>"


def build_summary_html(data: dict, complet_href: str) -> str:
    mode, today = data["mode"], data["today"]
    indices_subset = INDICES_MATIN if mode == "matin" else INDICES_SOIR
    section_title = "Nuit dernière (Asie / clôture US)" if mode == "matin" else "Clôture du jour (Europe / US)"
    calendar_title = "À surveiller aujourd'hui en Europe" if mode == "matin" else "Demain au calendrier économique"
    mode_label = "Matin" if mode == "matin" else "Soir"
    fx = data["fx"].get("EUR/USD")
    fx_line = (
        f'<div class="row"><span>EUR/USD</span><span>{fx["level"]:.4f} '
        f'<span class="{"up" if fx["change_pct"] >= 0 else "down"}">{fmt_pct(fx["change_pct"])}</span></span></div>'
        if fx else '<div class="row"><span>EUR/USD</span><span class="muted">indisponible</span></div>'
    )
    watchlist_card = ""
    if data.get("watchlist"):
        watchlist_card = f"""
<div class="card">
  <h2>Ma watchlist</h2>
  {html_index_rows(list(data["watchlist"].keys()), data["watchlist"])}
</div>
"""

    body = f"""
<span class="badge">{mode_label}</span>
<h1>Brief Marchés</h1>
<p class="subtitle">{format_date_fr(today)}</p>
{html_banners(data)}

<div class="card">
  <h2>{section_title}</h2>
  {html_index_rows(indices_subset, data["indices"])}
</div>

<div class="card">
  <h2>Volatilité &amp; matières premières</h2>
  {html_index_rows(EXTRA_ASSETS_SUMMARY, data["extra"])}
</div>
{watchlist_card}
<div class="card">
  <h2>Taux &amp; devises</h2>
  {html_rates_rows(data["rates"], RATE_LABELS_SUMMARY)}
  {fx_line}
</div>

<div class="card">
  <h2>{calendar_title}</h2>
  {html_calendar_list(data["calendar_target"])}
</div>

<div class="card">
  <h2>Actus macro / marchés</h2>
  {html_news_list(data["news"][:NEWS_ITEMS_SUMMARY])}
</div>

<a class="cta" href="{html.escape(complet_href)}">Voir le rapport complet →</a>

<footer>Généré le {data["generated_at"]} (Europe/Paris). Sources : Yahoo Finance, FRED, ForexFactory, Google News. Données indicatives, non temps réel.</footer>
"""
    return html_page(f"Brief Marchés — {mode_label} — {format_date_fr(today)}", body)


def build_full_html(data: dict, resume_href: str) -> str:
    mode, today = data["mode"], data["today"]
    mode_label = "Matin" if mode == "matin" else "Soir"
    index_names = list(ALL_INDICES.keys())
    extra_names = list(EXTRA_ASSETS.keys())
    watchlist_names = list(data.get("watchlist", {}).keys())
    combined = {**data["indices"], **data["extra"], **data.get("watchlist", {})}
    fx = data["fx"].get("EUR/USD")
    fx_line = (
        f'<div class="row"><span>EUR/USD</span><span>{fx["level"]:.4f} '
        f'<span class="{"up" if fx["change_pct"] >= 0 else "down"}">{fmt_pct(fx["change_pct"])}</span></span></div>'
        if fx else '<div class="row"><span>EUR/USD</span><span class="muted">indisponible</span></div>'
    )
    watchlist_card = ""
    if watchlist_names:
        watchlist_card = f"""
<div class="card">
  <h2>Ma watchlist</h2>
  {html_index_rows(watchlist_names, data["watchlist"], show_5d=True, show_ytd=True)}
</div>
"""

    body = f"""
<a class="back" href="{html.escape(resume_href)}">← Retour au résumé</a>
<span class="badge">{mode_label} — rapport complet</span>
<h1>Brief Marchés</h1>
<p class="subtitle">{format_date_fr(today)}</p>
{html_banners(data)}

<div class="card">
  <h2>Tous les indices (niveau actuel)</h2>
  {html_index_rows(index_names, data["indices"], show_5d=True, show_ytd=True)}
</div>

<div class="card">
  <h2>Volatilité &amp; matières premières (complet)</h2>
  {html_index_rows(extra_names, data["extra"], show_5d=True, show_ytd=True)}
</div>
{watchlist_card}
<div class="card">
  <h2>Historique 5 séances</h2>
  {html_index_history_tables(index_names + extra_names + watchlist_names, combined)}
</div>

<div class="card">
  <h2>Taux directeurs &amp; obligataires</h2>
  {html_rates_rows(data["rates"], list(RATE_SERIES_FULL.keys()))}
  {fx_line}
</div>

<div class="card">
  <h2>Calendrier économique de la semaine (USD/EUR, impact moyen+)</h2>
  {html_calendar_list(data["calendar_week"][:CALENDAR_ITEMS_FULL])}
</div>

<div class="card">
  <h2>Actus macro / marchés</h2>
  {html_news_list(data["news"])}
</div>

<footer>
  Généré le {data["generated_at"]} (Europe/Paris).<br>
  Sources : Yahoo Finance (indices, EUR/USD, volatilité, matières premières), FRED — Fed de St. Louis (taux),
  ForexFactory (calendrier), Google News (actus).<br>
  Le taux 10 ans France provient de la dernière publication mensuelle disponible (pas de source quotidienne gratuite fiable identifiée).
  Le calendrier ForexFactory est un flux non officiel, parfois temporairement limité.<br>
  Données indicatives, non temps réel — usage informatif uniquement, ne constitue pas un conseil en investissement.
</footer>
"""
    return html_page(f"Brief Marchés — {mode_label} (complet) — {format_date_fr(today)}", body)


# --------------------------------------------------------------------------
# Collecte + sauvegarde + ouverture + nettoyage
# --------------------------------------------------------------------------

def collect_data(mode: str, news_query: str, watchlist_path: Path | None = None) -> dict:
    today = datetime.now(PARIS_TZ).date()
    target_date = today if mode == "matin" else date.fromordinal(today.toordinal() + 1)

    indices = fetch_indices(ALL_INDICES)
    mark_staleness(indices, mode, today)
    extra = fetch_indices(EXTRA_ASSETS)
    fx = fetch_indices(FX)
    rates = fetch_rates()
    news = fetch_news(news_query, NEWS_ITEMS_FULL)
    calendar_week = fetch_calendar_week()
    watchlist_tickers = load_watchlist(watchlist_path) if watchlist_path else {}
    watchlist = fetch_indices(watchlist_tickers) if watchlist_tickers else {}

    primary_names = INDICES_MATIN if mode == "matin" else INDICES_SOIR
    primary_infos = [indices.get(n) for n in primary_names]
    market_closed = bool(primary_infos) and all(info is not None and info.get("stale") for info in primary_infos)

    data = {
        "mode": mode,
        "today": today,
        "target_date": target_date,
        "indices": indices,
        "extra": extra,
        "fx": fx,
        "rates": rates,
        "news": news,
        "calendar_week": calendar_week,
        "calendar_target": events_on(calendar_week, target_date),
        "watchlist": watchlist,
        "market_closed": market_closed,
        "generated_at": datetime.now(PARIS_TZ).strftime("%d/%m/%Y à %Hh%M"),
    }
    data["health"] = compute_health(data)
    data["big_moves"] = compute_big_moves(data)
    return data


def save_outputs(data: dict, output_dir: Path) -> dict[str, Path]:
    output_dir.mkdir(parents=True, exist_ok=True)
    today_str = data["today"].isoformat()
    mode = data["mode"]

    resume_name = f"{today_str}-{mode}-resume.html"
    complet_name = f"{today_str}-{mode}-complet.html"
    md_name = f"{today_str}-{mode}.md"

    resume_path = output_dir / resume_name
    complet_path = output_dir / complet_name
    md_path = output_dir / md_name

    resume_path.write_text(build_summary_html(data, complet_href=complet_name), encoding="utf-8")
    complet_path.write_text(build_full_html(data, resume_href=resume_name), encoding="utf-8")
    md_path.write_text(build_markdown(data), encoding="utf-8")

    return {"resume": resume_path, "complet": complet_path, "md": md_path}


def cleanup_old_briefs(output_dir: Path, keep_days: int) -> int:
    """Supprime les fichiers de brief datés de plus de keep_days jours."""
    if keep_days <= 0 or not output_dir.exists():
        return 0
    cutoff = date.fromordinal(datetime.now(PARIS_TZ).date().toordinal() - keep_days)
    removed = 0
    for path in output_dir.iterdir():
        if not path.is_file():
            continue
        m = BRIEF_FILE_RE.match(path.name)
        if not m:
            continue
        try:
            file_date = date.fromisoformat(m.group(1))
        except ValueError:
            continue
        if file_date < cutoff:
            path.unlink()
            removed += 1
    return removed


INDEX_FILE_RE = re.compile(r"^(\d{4}-\d{2}-\d{2})-(matin|soir)-resume\.html$")


def build_index_html(output_dir: Path) -> str:
    """Page listant tous les briefs archivés, avec liens vers chaque résumé."""
    entries: dict[str, dict[str, str]] = {}
    if output_dir.exists():
        for path in output_dir.iterdir():
            m = INDEX_FILE_RE.match(path.name)
            if m:
                entries.setdefault(m.group(1), {})[m.group(2)] = path.name

    rows = []
    for d in sorted(entries.keys(), reverse=True):
        try:
            label = format_date_fr(date.fromisoformat(d))
        except ValueError:
            label = d
        links = []
        for mode, mode_label in (("matin", "Matin"), ("soir", "Soir")):
            if mode in entries[d]:
                links.append(f'<a href="{html.escape(entries[d][mode])}">{mode_label}</a>')
        rows.append(f'<div class="row"><span>{html.escape(label)}</span><span>{" · ".join(links)}</span></div>')

    body = f"""
<h1>Historique des briefs marchés</h1>
<p class="subtitle">{len(entries)} jour(s) archivé(s)</p>
<div class="card">
{"".join(rows) if rows else "<p class='muted'>Aucun brief généré pour le moment.</p>"}
</div>
"""
    return html_page("Historique — Brief Marchés", body)


NOTIF_SHORT_NAMES = {
    "Nikkei 225": "Nikkei",
    "CAC 40": "CAC",
    "Eurostoxx 50": "SX5E",
    "S&P 500": "S&P",
    "Nasdaq": "Nasdaq",
}


def notification_summary(data: dict) -> str:
    mode = data["mode"]
    names = INDICES_MATIN if mode == "matin" else INDICES_SOIR
    parts = []
    for name in names:
        info = data["indices"].get(name)
        if info is None:
            continue
        short = NOTIF_SHORT_NAMES.get(name, name)
        parts.append(f"{short} {fmt_pct(info['change_pct'])}")
    return " · ".join(parts) if parts else "Données indisponibles aujourd'hui"


def send_notification(title: str, message: str) -> None:
    """Notification native macOS via osascript (no-op sur les autres plateformes)."""
    if sys.platform != "darwin":
        return

    def _q(s: str) -> str:
        return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'

    script = f"display notification {_q(message)} with title {_q(title)}"
    try:
        subprocess.run(["osascript", "-e", script], check=False, timeout=5)
    except Exception as exc:
        logging.warning("Notification macOS impossible : %s", exc)


def load_smtp_config() -> dict | None:
    """Configuration SMTP depuis des variables d'environnement (jamais en dur dans le code).

    Requiert MARKET_BRIEF_SMTP_USER et MARKET_BRIEF_SMTP_PASSWORD (mot de passe
    d'application pour Gmail). Si absentes, l'envoi d'email est simplement ignoré.
    """
    user = os.environ.get("MARKET_BRIEF_SMTP_USER")
    password = os.environ.get("MARKET_BRIEF_SMTP_PASSWORD")
    if not user or not password:
        return None
    return {
        "user": user,
        "password": password,
        "to": os.environ.get("MARKET_BRIEF_EMAIL_TO", user),
        "host": os.environ.get("MARKET_BRIEF_SMTP_HOST", "smtp.gmail.com"),
        "port": int(os.environ.get("MARKET_BRIEF_SMTP_PORT", "465")),
        "starttls": os.environ.get("MARKET_BRIEF_SMTP_STARTTLS", "0") == "1",
    }


def send_email(data: dict, html_body: str, cfg: dict) -> None:
    mode_label = "Matin" if data["mode"] == "matin" else "Soir"
    msg = EmailMessage()
    msg["Subject"] = f"Brief Marchés — {mode_label} — {format_date_fr(data['today'])}"
    msg["From"] = cfg["user"]
    msg["To"] = cfg["to"]
    msg.set_content("Ce message nécessite un client email compatible HTML.")
    msg.add_alternative(html_body, subtype="html")

    if cfg["starttls"]:
        with smtplib.SMTP(cfg["host"], cfg["port"], timeout=15) as server:
            server.starttls()
            server.login(cfg["user"], cfg["password"])
            server.send_message(msg)
    else:
        with smtplib.SMTP_SSL(cfg["host"], cfg["port"], timeout=15) as server:
            server.login(cfg["user"], cfg["password"])
            server.send_message(msg)


def open_in_browser(path: Path) -> None:
    try:
        if sys.platform == "darwin":
            subprocess.run(["open", str(path)], check=False)
        elif sys.platform.startswith("linux"):
            subprocess.run(["xdg-open", str(path)], check=False)
        else:
            logging.info("Ouverture automatique non supportée sur cette plateforme : %s", sys.platform)
    except Exception as exc:
        logging.warning("Impossible d'ouvrir automatiquement le brief : %s", exc)


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(description="Génère un brief quotidien des marchés financiers et de la macro.")
    parser.add_argument("mode", choices=["matin", "soir"], help="Mode du brief à générer")
    parser.add_argument("--output-dir", default=str(Path(__file__).parent / "briefs"), help="Dossier de sortie (défaut: briefs/)")
    parser.add_argument("--news-query", default=DEFAULT_NEWS_QUERY, help="Requête de recherche Google News personnalisée")
    parser.add_argument("--no-open", action="store_true", help="Ne pas ouvrir automatiquement le résumé à l'écran")
    parser.add_argument("--no-notify", action="store_true", help="Ne pas envoyer de notification macOS")
    parser.add_argument("--no-email", action="store_true", help="Ne pas envoyer d'email même si MARKET_BRIEF_SMTP_* est configuré")
    parser.add_argument(
        "--watchlist",
        default=str(Path(__file__).parent / "watchlist.json"),
        help="Fichier JSON {\"tickers\": {nom: symbole}} de valeurs personnalisées à suivre (défaut: watchlist.json)",
    )
    parser.add_argument("--keep-days", type=int, default=90, help="Jours d'historique à conserver avant purge (défaut: 90)")
    parser.add_argument("--no-cleanup", action="store_true", help="Ne pas purger les anciens briefs")
    parser.add_argument("--quiet", action="store_true", help="N'affiche que les erreurs sur la sortie standard")
    parser.add_argument(
        "--only-if-hour",
        type=int,
        default=None,
        help=(
            "N'exécute rien si l'heure locale Europe/Paris actuelle n'est pas celle-ci (0-23). "
            "Utile pour un planning GitHub Actions en UTC qui doit couvrir les deux horaires "
            "d'heure d'été/d'hiver sans dupliquer les envois."
        ),
    )
    args = parser.parse_args()

    logging.basicConfig(level=logging.ERROR if args.quiet else logging.WARNING, format="%(levelname)s: %(message)s")

    if args.only_if_hour is not None:
        current_hour = datetime.now(PARIS_TZ).hour
        if current_hour != args.only_if_hour:
            print(
                f"Heure locale Europe/Paris actuelle ({current_hour}h) différente de la cible "
                f"({args.only_if_hour}h) — exécution ignorée (probablement l'autre créneau UTC/DST)."
            )
            return

    data = collect_data(args.mode, args.news_query, Path(args.watchlist))
    output_dir = Path(args.output_dir)
    paths = save_outputs(data, output_dir)

    if data["health"]["degraded"]:
        logging.error("Brief dégradé : sources indisponibles (%s).", ", ".join(data["health"]["failing_categories"]))
        if "indices/devises/matières premières" in data["health"]["failing_categories"]:
            logging.error(
                "Cause fréquente : yfinance désynchronisé avec Yahoo Finance. Essayez : "
                "%s -m pip install --upgrade yfinance", sys.executable
            )

    print(build_markdown(data))
    print(f"\nRésumé  : {paths['resume']}")
    print(f"Complet : {paths['complet']}")
    print(f"Archive : {paths['md']}")

    if not args.no_cleanup:
        removed = cleanup_old_briefs(output_dir, args.keep_days)
        if removed:
            print(f"Nettoyage : {removed} ancien(s) fichier(s) supprimé(s) (> {args.keep_days} jours).")

    index_path = output_dir / "index.html"
    index_path.write_text(build_index_html(output_dir), encoding="utf-8")
    print(f"Index   : {index_path}")

    if not args.no_notify:
        mode_label = "Matin" if args.mode == "matin" else "Soir"
        send_notification(f"Brief Marchés — {mode_label}", notification_summary(data))

    if not args.no_email:
        smtp_config = load_smtp_config()
        if smtp_config:
            try:
                email_body = build_summary_html(data, complet_href="#")
                send_email(data, email_body, smtp_config)
                print(f"Email   : envoyé à {smtp_config['to']}")
            except Exception as exc:
                logging.error("Échec de l'envoi de l'email : %s", exc)

    if not args.no_open:
        open_in_browser(paths["resume"])

    sys.exit(1 if data["health"]["degraded"] else 0)


if __name__ == "__main__":
    main()
