#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Combinador POV Studio
Embaralha takes, aplica ganchos de texto + seta de carrinho e renderiza em lote.

Principais pontos desta versão:
  * Renderização em paralelo, com barra de progresso por vídeo, ETA e botão cancelar.
  * Overlay do gancho recortado só na área do texto (bem mais leve para o ffmpeg).
  * Preset mais rápido e uso automático de GPU (NVENC / QuickSync) quando disponível.
  * Interface não trava durante o render (tudo roda em threads).
  * Dashboard com miniaturas dos takes, prévia animada (clique/arraste para mover a seta),
    fila filtrável e configurações salvas automaticamente.
"""

import os
import re
import sys
import glob
import json
import math
import time
import queue
import random
import shutil
import hashlib
import itertools
import threading
import traceback
import subprocess
import urllib.request
from concurrent.futures import ThreadPoolExecutor
import tkinter as tk
from tkinter import filedialog, messagebox, ttk

try:
    import customtkinter as ctk
    from PIL import Image, ImageDraw, ImageFont
except Exception as e:  # biblioteca ausente
    _r = tk.Tk()
    _r.withdraw()
    messagebox.showerror("Erro ao iniciar", f"Biblioteca ausente:\n{e}")
    sys.exit(1)


def _garantir_ffmpeg():
    """No .exe o ffmpeg vem embutido (imageio-ffmpeg). Se não houver ffmpeg no PATH,
    copia o embutido como 'ffmpeg.exe' para uma pasta de cache e a coloca no PATH."""
    if shutil.which("ffmpeg"):
        return
    try:
        import imageio_ffmpeg
        origem = imageio_ffmpeg.get_ffmpeg_exe()
        pasta = os.path.join(os.path.expanduser("~"), ".combinador_fonts", "bin")
        os.makedirs(pasta, exist_ok=True)
        destino = os.path.join(pasta, "ffmpeg.exe" if os.name == "nt" else "ffmpeg")
        if not os.path.exists(destino) or os.path.getsize(destino) != os.path.getsize(origem):
            shutil.copy2(origem, destino)
        os.environ["PATH"] = pasta + os.pathsep + os.environ.get("PATH", "")
    except Exception:
        pass


_garantir_ffmpeg()

# ───────────────────────────── Tema ─────────────────────────────
BG_MAIN = "#0A0E16"
BG_CARD = "#121826"
BG_ITEM = "#182033"
BG_INPUT = "#0D1220"
BORDER_COLOR = "#222C42"
BTN_NEUTRAL = "#1E293B"
BTN_HOVER = "#334155"
ACCENT = "#6366F1"
ACCENT_HOVER = "#4F46E5"
ACCENT_SOFT = "#818CF8"
ORANGE = "#FF5500"
ORANGE_SOFT = "#FB923C"
SUCCESS = "#10B981"
SUCCESS_HOVER = "#059669"
OK_BG = "#064E3B"
OK_TX = "#34D399"
DANGER = "#EF4444"
DANGER_BG = "#7F1D1D"
DANGER_TX = "#FCA5A5"
WARN = "#F59E0B"
TEXT_MAIN = "#F1F5F9"
TEXT_MUTED = "#8B97AD"

ctk.set_appearance_mode("Dark")

# ───────────────────────────── Constantes ─────────────────────────────
CROP_PX = 4            # corte de cada lado (blindagem do vídeo)
ARROW_BASE_PX = 110    # tamanho da seta em um vídeo de 1080 de largura
ARROW_AMP_PX = 18      # amplitude do balanço em 1080 de largura
PV_W, PV_H = 234, 416  # tamanho da prévia lateral (9:16)
LANCZOS = getattr(Image, "Resampling", Image).LANCZOS
NO_WINDOW = {"creationflags": 0x08000000} if os.name == "nt" else {}

SPEEDS = {
    "Rápido (recomendado)": "veryfast",
    "Turbo (arquivo maior)": "ultrafast",
    "Equilibrado": "fast",
}
HW_CANDIDATES = [
    ("NVIDIA NVENC", "h264_nvenc", ["-preset", "p4", "-rc", "vbr", "-cq", "{q}", "-b:v", "0"]),
    ("Intel QuickSync", "h264_qsv", ["-global_quality", "{q}", "-preset", "veryfast"]),
]
PROGRESS_KEYS = {
    "frame", "fps", "bitrate", "total_size", "out_time_us", "out_time_ms", "out_time",
    "dup_frames", "drop_frames", "speed", "progress",
}
STATUS_TXT = {"queue": "Na fila", "run": "Gerando", "done": "Pronto", "fail": "Falhou", "cancel": "Cancelado"}


# ───────────────────────────── Utilitários ─────────────────────────────
def fmt_time(seconds):
    s = max(0, int(seconds))
    h, rest = divmod(s, 3600)
    m, s = divmod(rest, 60)
    return f"{h}:{m:02d}:{s:02d}" if h else f"{m:02d}:{s:02d}"


def open_path(path):
    try:
        if sys.platform.startswith("win"):
            os.startfile(path)  # noqa
        elif sys.platform == "darwin":
            subprocess.Popen(["open", path])
        else:
            subprocess.Popen(["xdg-open", path])
    except Exception as e:
        messagebox.showerror("Erro", f"Não consegui abrir:\n{path}\n\n{e}")


def probe_media(path):
    """Lê duração e resolução (já considerando rotação) usando só o ffmpeg."""
    try:
        r = subprocess.run(["ffmpeg", "-hide_banner", "-i", path], stdout=subprocess.PIPE,
                           stderr=subprocess.PIPE, text=True, encoding="utf-8", errors="replace", **NO_WINDOW)
    except Exception:
        return None
    txt = r.stderr or ""
    info = {"duration": 0.0, "w": 0, "h": 0}
    m = re.search(r"Duration:\s*(\d+):(\d+):(\d+(?:\.\d+)?)", txt)
    if m:
        info["duration"] = int(m.group(1)) * 3600 + int(m.group(2)) * 60 + float(m.group(3))
    m = re.search(r"Video:.*?,\s*(\d{2,5})x(\d{2,5})", txt)
    if m:
        w, h = int(m.group(1)), int(m.group(2))
        rot = re.search(r"rotation of (-?\d+(?:\.\d+)?) degrees", txt)
        if rot and abs(round(float(rot.group(1)))) in (90, 270):
            w, h = h, w
        info["w"], info["h"] = w, h
    return info


def load_font(path, size):
    if path and os.path.exists(path):
        try:
            font = ImageFont.truetype(path, size=size)
            try:
                font.set_variation_by_name("Bold")
            except Exception:
                try:
                    font.set_variation_by_axes([36, 100, 700, 0])
                except Exception:
                    pass
            return font
        except Exception:
            pass
    return ImageFont.load_default()


def wrap_text(text, font, stroke, max_w):
    draw = ImageDraw.Draw(Image.new("RGBA", (10, 10)))
    words = text.split()
    if not words:
        return []
    lines, cur = [], words[0]
    for word in words[1:]:
        test = f"{cur} {word}"
        try:
            b = draw.textbbox((0, 0), test, font=font, stroke_width=stroke)
            w = b[2] - b[0]
        except Exception:
            w = len(test) * getattr(font, "size", 20) * 0.52
        if w <= max_w:
            cur = test
        else:
            lines.append(cur)
            cur = word
    if cur:
        lines.append(cur)
    return lines


def render_hook_overlay(cfg, text, cw, ch, jitter):
    """Desenha o gancho (texto branco com contorno preto ou caixa escura) num canvas transparente."""
    img = Image.new("RGBA", (cw, ch), (0, 0, 0, 0))
    draw = ImageDraw.Draw(img)
    base_size, base_stroke = cfg["font_size"], cfg["stroke"]
    font_ref = load_font(cfg["font_path"], base_size)
    lines = wrap_text(text, font_ref, base_stroke, int(1080 * cfg["max_w"]))

    k = cw / 1080.0
    fsize = max(6, int(round(base_size * k)))
    stroke = max(1, int(round(base_stroke * k)))
    font = load_font(cfg["font_path"], fsize)

    y_pct = cfg["text_y"]
    x_jit = 0
    if jitter:
        y_pct += random.uniform(-0.005, 0.005)
        x_jit = int(random.randint(-6, 6) * k)
    y_base = int(ch * y_pct)
    spacing = int(fsize * 1.35)
    box_style = "Caixa Escura" in cfg["style"]

    for n, line in enumerate(lines):
        try:
            b = draw.textbbox((0, 0), line, font=font, stroke_width=stroke)
            tw, th = b[2] - b[0], b[3] - b[1]
        except Exception:
            tw, th = int(len(line) * fsize * 0.52), fsize
        x = int((cw - tw) / 2) + x_jit
        y = y_base + n * spacing
        if box_style:
            px, py = int(16 * k), int(10 * k)
            box = [x - px, y - py, x + tw + px, y + th + py]
            try:
                draw.rounded_rectangle(box, radius=int(12 * k), fill=(0, 0, 0, 175))
            except Exception:
                draw.rectangle(box, fill=(0, 0, 0, 175))
            draw.text((x, y), line, font=font, fill=(255, 255, 255, 255))
        else:
            off = max(2, int(3 * k))
            try:
                draw.text((x, y + off), line, font=font, fill=(0, 0, 0, 150),
                          stroke_width=stroke + max(1, int(2 * k)), stroke_fill=(0, 0, 0, 110))
                draw.text((x, y), line, font=font, fill=(255, 255, 255, 255),
                          stroke_width=stroke, stroke_fill=(0, 0, 0, 255))
            except TypeError:
                for dx in range(-stroke, stroke + 1):
                    for dy in range(-stroke, stroke + 1):
                        if dx * dx + dy * dy <= stroke * stroke:
                            draw.text((x + dx, y + dy), line, font=font, fill=(0, 0, 0, 255))
                draw.text((x, y), line, font=font, fill=(255, 255, 255, 255))
    return img


def save_trimmed_overlay(img, path):
    """Salva só a área com texto. Overlay pequeno = ffmpeg muito mais rápido. Devolve (x, y) ou None."""
    bbox = img.getbbox()
    if not bbox:
        return None
    pad = 6
    l = max(0, bbox[0] - pad)
    t = max(0, bbox[1] - pad)
    r = min(img.size[0], bbox[2] + pad)
    b = min(img.size[1], bbox[3] + pad)
    l -= l % 2
    t -= t % 2
    img.crop((l, t, r, b)).save(path, "PNG")
    return l, t


def prepare_arrow_png(src, px, cache_dir):
    """Redimensiona a seta (PNG/WEBP) uma única vez. GIFs são escalados pelo próprio ffmpeg."""
    if not src or not os.path.exists(src) or src.lower().endswith(".gif"):
        return None
    try:
        key = hashlib.md5(f"{src}|{os.path.getmtime(src)}|{px}".encode()).hexdigest()[:12]
        dest = os.path.join(cache_dir, f"arrow_{key}.png")
        if not os.path.exists(dest):
            Image.open(src).convert("RGBA").resize((px, px), LANCZOS).save(dest, "PNG")
        return dest
    except Exception:
        return None


def test_encoder(codec, extra):
    cmd = ["ffmpeg", "-hide_banner", "-loglevel", "error", "-f", "lavfi", "-i",
           "color=c=black:s=640x360:d=0.3:r=30", "-frames:v", "5", "-c:v", codec]
    cmd += [a.replace("{q}", "23") for a in extra]
    cmd += ["-pix_fmt", "yuv420p", "-f", "null", "-"]
    try:
        r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=25, **NO_WINDOW)
        return r.returncode == 0
    except Exception:
        return False


def build_command(cfg, files, out_path, prefix, hook_text, limit=None, with_audio=True):
    """Monta o comando do ffmpeg. Devolve (cmd, arquivos_temporários)."""
    temps = []
    list_path = prefix + "_list.txt"
    with open(list_path, "w", encoding="utf-8") as f:
        for p in files:
            f.write("file '" + p.replace("'", "'\\''") + "'\n")
    temps.append(list_path)

    cmd = ["ffmpeg", "-y", "-hide_banner", "-nostats", "-loglevel", "error", "-progress", "pipe:1",
           "-f", "concat", "-safe", "0", "-i", list_path]
    idx = 1
    audio_idx = hook_idx = arrow_idx = None
    out_w, out_h = cfg["out_w"], cfg["out_h"]

    if with_audio and cfg["audio"]:
        cmd += ["-i", cfg["audio"]]
        audio_idx = idx
        idx += 1

    hook_xy = None
    if cfg["hooks_on"] and hook_text:
        layer = render_hook_overlay(cfg, hook_text, out_w, out_h, True)
        hook_png = prefix + "_hook.png"
        hook_xy = save_trimmed_overlay(layer, hook_png)
        if hook_xy:
            temps.append(hook_png)
            cmd += ["-i", hook_png]
            hook_idx = idx
            idx += 1

    arrow_is_gif = False
    if cfg["arrow_on"] and cfg["arrow_path"] and os.path.exists(cfg["arrow_path"]):
        arrow_is_gif = cfg["arrow_path"].lower().endswith(".gif")
        if arrow_is_gif:
            cmd += ["-ignore_loop", "0", "-i", cfg["arrow_path"]]
        elif cfg.get("arrow_png"):
            cmd += ["-i", cfg["arrow_png"]]
        else:
            cmd += ["-loop", "1", "-framerate", "30", "-i", cfg["arrow_path"]]
            arrow_is_gif = True  # mesma lógica de "shortest" e escala
        arrow_idx = idx
        idx += 1

    base = f"crop=iw-{2 * CROP_PX}:ih-{2 * CROP_PX}:{CROP_PX}:{CROP_PX}"
    if hook_idx is None and arrow_idx is None:
        cmd += ["-vf", f"{base},format=yuv420p", "-map", "0:v:0"]
    else:
        parts = [f"[0:v]{base}[v0]"]
        cur = "[v0]"
        if hook_idx is not None:
            parts.append(f"{cur}[{hook_idx}:v]overlay={hook_xy[0]}:{hook_xy[1]}:format=auto[v_hook]")
            cur = "[v_hook]"
        if arrow_idx is not None:
            xr = cfg["arrow_x"] + random.uniform(-0.003, 0.003)
            yr = cfg["arrow_y"] + random.uniform(-0.003, 0.003)
            amp = ARROW_AMP_PX * out_w / 1080.0
            mode = cfg["arrow_anim"]
            bounce = f"y='H*{yr:.4f}+{amp:.1f}*sin(t*9)'"
            still = f"y='H*{yr:.4f}'"
            xexp = f"x='W*{xr:.4f}'"
            short = ":shortest=1" if arrow_is_gif else ""
            if "Balançando + Piscando" in mode:
                ov = f"{xexp}:{bounce}:enable='gt(mod(t,0.75),0.18)'{short}:format=auto"
            elif "Piscando Rápido" in mode:
                ov = f"{xexp}:{still}:enable='gt(mod(t,0.55),0.20)'{short}:format=auto"
            else:
                ov = f"{xexp}:{bounce}{short}:format=auto"
            ap = cfg["arrow_px"]
            if arrow_is_gif:
                parts.append(f"[{arrow_idx}:v]scale={ap}:{ap},format=rgba[arrow_img]")
            else:
                parts.append(f"[{arrow_idx}:v]format=rgba[arrow_img]")
            parts.append(f"{cur}[arrow_img]overlay={ov}[v_arr]")
            cur = "[v_arr]"
        parts.append(f"{cur}format=yuv420p[v_out]")
        cmd += ["-filter_complex", ";".join(parts), "-map", "[v_out]"]

    if not with_audio:
        cmd += ["-an"]
    else:
        pitch = random.uniform(1.004, 1.006)
        af = f"asetrate=44100*{pitch:.5f},aresample=44100"
        if audio_idx is not None:
            cmd += ["-map", f"{audio_idx}:a:0", "-af", af, "-shortest"]
        else:
            cmd += ["-map", "0:a:0?", "-af", af]

    crf = random.choice([21, 22, 23])
    if cfg.get("hw"):
        codec, extra = cfg["hw"]
        cmd += ["-c:v", codec] + [a.replace("{q}", str(crf + 1)) for a in extra]
    else:
        cmd += ["-c:v", "libx264", "-preset", cfg["preset"], "-crf", str(crf)]
    cmd += ["-pix_fmt", "yuv420p", "-c:a", "aac", "-b:a", "192k", "-map_metadata", "-1"]
    if limit:
        cmd += ["-t", str(limit)]
    cmd.append(out_path)
    return cmd, temps


# ───────────────────────────── Aplicativo ─────────────────────────────
class VideoCombinerApp(ctk.CTk):
    def __init__(self):
        super().__init__()
        self.title("Combinador POV Studio")
        try:
            scale = float(self._get_window_scaling())
        except Exception:
            scale = 1.0
        w = min(1400, int(self.winfo_screenwidth() / scale * 0.96))
        h = min(900, int(self.winfo_screenheight() / scale * 0.90))
        self.geometry(f"{w}x{h}+10+10")
        self.minsize(1080, 640)
        self.resizable(True, True)
        self.configure(fg_color=BG_MAIN)
        self.after(250, self._maximize)

        # Estado
        self.files = {i: None for i in range(1, 6)}
        self.take_info = {}
        self.take_frames = {}
        self.audio_file = None
        self.audio_dur = 0.0
        self.output_folder = None
        self.custom_font_path = None
        self.custom_arrow_path = None
        self.combinations = []
        self.status = {}
        self.prog_pct = {}
        self.errors = {}
        self.out_paths = {}
        self.filter_mode = "Todos"
        self.hook_idx = 0
        self.hw_encoder = None  # (nome, codec, args)
        self.hw_name = None

        # Render
        self.ui_q = queue.Queue()
        self.cancel_event = threading.Event()
        self.procs = set()
        self.proc_lock = threading.Lock()
        self.rendering = False
        self.batch_idx = []
        self.job_prog = {}
        self.batch_start = 0.0

        # Prévia
        self._pv = None
        self._pv_job = None
        self._pv_img = None
        self._pv_bg_cache = {}
        self._anim_t0 = time.time()

        # Pastas auxiliares
        self.assets_dir = os.path.join(os.path.expanduser("~"), ".combinador_fonts")
        self.tmp_dir = os.path.join(self.assets_dir, "tmp")
        self.arrow_cache = os.path.join(self.assets_dir, "arrow_cache")
        for d in (self.assets_dir, self.tmp_dir, self.arrow_cache):
            os.makedirs(d, exist_ok=True)
        self.saved_font_config = os.path.join(self.assets_dir, "last_custom_font.txt")
        self.settings_path = os.path.join(self.assets_dir, "settings.json")

        self.auto_detect_tiktok_font()
        self.generate_builtin_arrows()
        self.blank_img = ctk.CTkImage(Image.new("RGBA", (34, 56), (13, 18, 32, 255)), size=(34, 56))

        self._setup_styles()
        self.create_widgets()
        self.load_settings()
        self.update_chips()

        self.protocol("WM_DELETE_WINDOW", self.on_close)
        self.after(40, self._drain_ui)
        self.after(500, self._tick_stats)
        self.after(120, self._anim_tick)
        self.after(150, self.refresh_embedded_preview)

        threading.Thread(target=self._bg_download_fonts, daemon=True).start()
        threading.Thread(target=self._bg_detect_encoders, daemon=True).start()

    # ───────────── infraestrutura ─────────────
    def _maximize(self):
        try:
            self.state("zoomed")
        except Exception:
            try:
                self.attributes("-zoomed", True)
            except Exception:
                pass

    def _drain_ui(self):
        try:
            for _ in range(300):
                fn = self.ui_q.get_nowait()
                try:
                    fn()
                except Exception:
                    traceback.print_exc()
        except queue.Empty:
            pass
        self.after(40, self._drain_ui)

    def _setup_styles(self):
        st = ttk.Style(self)
        try:
            st.theme_use("clam")
        except Exception:
            pass
        st.configure("Dash.Treeview", background=BG_ITEM, fieldbackground=BG_ITEM, foreground=TEXT_MAIN,
                     rowheight=28, borderwidth=0, relief="flat")
        st.map("Dash.Treeview", background=[("selected", "#2B3A67")], foreground=[("selected", TEXT_MAIN)])
        st.configure("Dash.Treeview.Heading", background=BG_CARD, foreground=TEXT_MUTED, relief="flat",
                     borderwidth=0, padding=(8, 6))
        st.map("Dash.Treeview.Heading", background=[("active", BG_CARD)])
        st.layout("Dash.Treeview", [("Treeview.treearea", {"sticky": "nswe"})])

    def _bg_download_fonts(self):
        urls = {
            "Poppins-Bold.ttf": "https://raw.githubusercontent.com/google/fonts/main/ofl/poppins/Poppins-Bold.ttf",
            "Poppins-SemiBold.ttf": "https://raw.githubusercontent.com/google/fonts/main/ofl/poppins/Poppins-SemiBold.ttf",
        }
        baixou = False
        for filename, url in urls.items():
            dest = os.path.join(self.assets_dir, filename)
            if os.path.exists(dest):
                continue
            try:
                req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
                with urllib.request.urlopen(req, timeout=6) as resp, open(dest, "wb") as out:
                    out.write(resp.read())
                baixou = True
            except Exception as e:
                print(f"Aviso ao baixar a fonte {filename}: {e}")
        if baixou:
            self.ui_q.put(self.schedule_preview)

    def _bg_detect_encoders(self):
        if not shutil.which("ffmpeg"):
            self.ui_q.put(lambda: self.lbl_encoder.configure(text="ffmpeg não encontrado", text_color=DANGER_TX))
            return
        for name, codec, extra in HW_CANDIDATES:
            if test_encoder(codec, extra):
                self.hw_encoder = (name, codec, extra)
                break
        self.ui_q.put(self._update_encoder_badge)

    def _update_encoder_badge(self):
        use_hw = self.hw_encoder and self.encoder_selector.get().startswith("Auto")
        if use_hw:
            self.lbl_encoder.configure(text=f"GPU: {self.hw_encoder[0]}", text_color=OK_TX)
        else:
            self.lbl_encoder.configure(text="CPU (x264)", text_color=TEXT_MUTED)
        detectado = f"Detectado: {self.hw_encoder[0]}" if self.hw_encoder else "Nenhuma GPU compatível detectada"
        self.lbl_encoder_hint.configure(text=detectado)

    # ───────────── fontes e setas ─────────────
    def auto_detect_tiktok_font(self):
        if os.path.exists(self.saved_font_config):
            try:
                with open(self.saved_font_config, "r", encoding="utf-8") as f:
                    saved = f.read().strip()
                if os.path.exists(saved):
                    self.custom_font_path = saved
                    return
            except Exception:
                pass
        try:
            script_dir = os.path.dirname(os.path.abspath(__file__))
        except Exception:
            script_dir = os.getcwd()
        for d in (os.getcwd(), script_dir, os.path.join(os.path.expanduser("~"), "Downloads"),
                  os.path.join(os.path.expanduser("~"), "Transferências")):
            if not os.path.exists(d):
                continue
            matches = glob.glob(os.path.join(d, "*[Tt]ik[Tt]ok*.ttf")) + glob.glob(os.path.join(d, "*[Tt]ik[Tt]ok*.otf"))
            if matches:
                dest = os.path.join(self.assets_dir, os.path.basename(matches[0]))
                try:
                    shutil.copy2(matches[0], dest)
                    self.custom_font_path = dest
                    with open(self.saved_font_config, "w", encoding="utf-8") as f:
                        f.write(dest)
                except Exception:
                    self.custom_font_path = matches[0]
                return

    def generate_builtin_arrows(self):
        styles = {"laranja": (255, 85, 0, 255), "amarela": (255, 215, 0, 255), "branca": (255, 255, 255, 255)}
        pts = [(155, 35), (285, 35), (285, 220), (380, 220), (220, 395), (60, 220), (155, 220)]
        for name, fill in styles.items():
            path = os.path.join(self.assets_dir, f"arrow_{name}.png")
            if os.path.exists(path):
                continue
            size = 440
            img = Image.new("RGBA", (size, size), (0, 0, 0, 0))
            d = ImageDraw.Draw(img)
            d.polygon([(x + 12, y + 14) for x, y in pts], fill=(0, 0, 0, 140))
            d.polygon(pts, fill=fill)
            d.line(pts + [pts[0]], fill=(10, 10, 10, 255), width=22)
            img.resize((115, 115), LANCZOS).save(path, "PNG")

    def get_resolved_font_path(self):
        choice = self.font_selector.get()
        bold = os.path.join(self.assets_dir, "Poppins-Bold.ttf")
        semi = os.path.join(self.assets_dir, "Poppins-SemiBold.ttf")
        if "TikTok Sans" in choice and self.custom_font_path and os.path.exists(self.custom_font_path):
            return self.custom_font_path
        if "Poppins Bold" in choice and os.path.exists(bold):
            return bold
        if "Poppins SemiBold" in choice and os.path.exists(semi):
            return semi
        if self.custom_font_path and os.path.exists(self.custom_font_path):
            return self.custom_font_path
        if os.path.exists(bold):
            return bold
        for fp in ("/usr/share/fonts/truetype/ubuntu/Ubuntu-B.ttf",
                   "/usr/share/fonts/truetype/liberation/LiberationSans-Bold.ttf"):
            if os.path.exists(fp):
                return fp
        return None

    def get_arrow_image_path(self):
        style = self.arrow_style_selector.get()
        if "Customizada" in style and self.custom_arrow_path and os.path.exists(self.custom_arrow_path):
            return self.custom_arrow_path
        if "Amarela" in style:
            return os.path.join(self.assets_dir, "arrow_amarela.png")
        if "Branca" in style:
            return os.path.join(self.assets_dir, "arrow_branca.png")
        return os.path.join(self.assets_dir, "arrow_laranja.png")

    # ───────────── construção da interface ─────────────
    def create_widgets(self):
        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(1, weight=1)
        self._build_header()

        body = ctk.CTkFrame(self, fg_color="transparent")
        body.grid(row=1, column=0, sticky="nsew", padx=16, pady=(0, 14))
        body.grid_columnconfigure(0, minsize=320)
        body.grid_columnconfigure(1, weight=1)
        body.grid_columnconfigure(2, minsize=272)
        body.grid_rowconfigure(0, weight=1)

        self._build_takes_column(body)
        self._build_center_column(body)
        self._build_preview_column(body)

    def _card(self, parent, **kw):
        return ctk.CTkFrame(parent, fg_color=BG_CARD, corner_radius=14, border_width=1,
                            border_color=BORDER_COLOR, **kw)

    def _build_header(self):
        head = ctk.CTkFrame(self, fg_color="transparent")
        head.grid(row=0, column=0, sticky="ew", padx=16, pady=(12, 10))

        left = ctk.CTkFrame(head, fg_color="transparent")
        left.pack(side="left")
        ctk.CTkLabel(left, text="Combinador POV Studio", font=ctk.CTkFont(size=22, weight="bold"),
                     text_color=TEXT_MAIN).pack(anchor="w")
        ctk.CTkLabel(left, text="Embaralhe takes, aplique ganchos e seta, renderize o lote.",
                     font=ctk.CTkFont(size=12), text_color=TEXT_MUTED).pack(anchor="w")

        right = ctk.CTkFrame(head, fg_color="transparent")
        right.pack(side="right")
        self.chips = {}
        for key, caption in (("takes", "Takes"), ("combos", "Variações"), ("done", "Prontos"), ("eta", "Tempo restante")):
            chip = ctk.CTkFrame(right, fg_color=BG_CARD, corner_radius=12, border_width=1, border_color=BORDER_COLOR)
            chip.pack(side="left", padx=4)
            val = ctk.CTkLabel(chip, text="0", font=ctk.CTkFont(size=17, weight="bold"), text_color=TEXT_MAIN)
            val.pack(padx=16, pady=(6, 0))
            ctk.CTkLabel(chip, text=caption, font=ctk.CTkFont(size=10), text_color=TEXT_MUTED).pack(padx=16, pady=(0, 6))
            self.chips[key] = val
        enc = ctk.CTkFrame(right, fg_color=BG_CARD, corner_radius=12, border_width=1, border_color=BORDER_COLOR)
        enc.pack(side="left", padx=(4, 0))
        self.lbl_encoder = ctk.CTkLabel(enc, text="Detectando...", font=ctk.CTkFont(size=12, weight="bold"),
                                        text_color=TEXT_MUTED)
        self.lbl_encoder.pack(padx=16, pady=(6, 0))
        ctk.CTkLabel(enc, text="Codificador", font=ctk.CTkFont(size=10), text_color=TEXT_MUTED).pack(padx=16, pady=(0, 6))

    # --- Coluna 1: takes ---
    def _build_takes_column(self, body):
        col = self._card(body)
        col.grid(row=0, column=0, sticky="nsew", padx=(0, 12))

        top = ctk.CTkFrame(col, fg_color="transparent")
        top.pack(fill="x", padx=14, pady=(12, 2))
        ctk.CTkLabel(top, text="Takes", font=ctk.CTkFont(size=15, weight="bold"), text_color=TEXT_MAIN).pack(side="left")
        ctk.CTkButton(top, text="Carregar 5 de uma vez", width=140, height=26, corner_radius=8, fg_color=BTN_NEUTRAL,
                      hover_color=BTN_HOVER, font=ctk.CTkFont(size=11, weight="bold"),
                      command=self.select_many).pack(side="right")
        ctk.CTkLabel(col, text="Clique em um cartão para escolher o vídeo.", font=ctk.CTkFont(size=11),
                     text_color=TEXT_MUTED, anchor="w").pack(fill="x", padx=14, pady=(0, 6))

        self.take_widgets = {}
        for i in range(1, 6):
            self._build_take_row(col, i)

        ctk.CTkFrame(col, height=1, fg_color=BORDER_COLOR).pack(fill="x", padx=14, pady=10)

        ctk.CTkLabel(col, text="Áudio", font=ctk.CTkFont(size=13, weight="bold"), text_color=TEXT_MAIN,
                     anchor="w").pack(fill="x", padx=14)
        arow = ctk.CTkFrame(col, fg_color="transparent")
        arow.pack(fill="x", padx=14, pady=(4, 0))
        self.btn_audio = ctk.CTkButton(arow, text="🎵 Escolher áudio", width=130, height=30, corner_radius=8,
                                       fg_color=BTN_NEUTRAL, hover_color=BTN_HOVER,
                                       font=ctk.CTkFont(size=12, weight="bold"), command=self.select_audio)
        self.btn_audio.pack(side="left")
        self.btn_audio_clear = ctk.CTkButton(arow, text="✕", width=28, height=30, corner_radius=8,
                                             fg_color="transparent", hover_color=BTN_HOVER, text_color=TEXT_MUTED,
                                             command=self.clear_audio)
        self.btn_audio_clear.pack(side="right")
        self.lbl_audio = ctk.CTkLabel(arow, text="Mantém o som dos takes", font=ctk.CTkFont(size=11),
                                      text_color=TEXT_MUTED, anchor="w")
        self.lbl_audio.pack(side="left", padx=10, fill="x", expand=True)

    def _build_take_row(self, parent, i):
        row = ctk.CTkFrame(parent, fg_color=BG_ITEM, corner_radius=10, height=64)
        row.pack(fill="x", padx=12, pady=3)
        row.pack_propagate(False)
        thumb = ctk.CTkLabel(row, text="＋", image=self.blank_img, compound="center", width=34, height=56,
                             fg_color=BG_INPUT, corner_radius=6, text_color=TEXT_MUTED, font=ctk.CTkFont(size=16))
        thumb.pack(side="left", padx=(8, 10), pady=4)
        mid = ctk.CTkFrame(row, fg_color="transparent")
        mid.pack(side="left", fill="both", expand=True, pady=8)
        name = ctk.CTkLabel(mid, text=f"Take {i}", anchor="w", font=ctk.CTkFont(size=12, weight="bold"),
                            text_color=TEXT_MAIN)
        name.pack(fill="x")
        meta = ctk.CTkLabel(mid, text="Escolher vídeo", anchor="w", font=ctk.CTkFont(size=11), text_color=TEXT_MUTED)
        meta.pack(fill="x")
        clear = ctk.CTkButton(row, text="✕", width=24, height=24, corner_radius=6, fg_color="transparent",
                              hover_color=BTN_HOVER, text_color=TEXT_MUTED, command=lambda n=i: self.clear_take(n))
        clear.pack(side="right", padx=8)
        for w in (row, thumb, mid, name, meta):
            w.bind("<Button-1>", lambda e, n=i: self.select_file(n))
        self.take_widgets[i] = {"row": row, "thumb": thumb, "name": name, "meta": meta}

    # --- Coluna 2: abas + fila ---
    def _build_center_column(self, body):
        center = ctk.CTkFrame(body, fg_color="transparent")
        center.grid(row=0, column=1, sticky="nsew")
        center.grid_columnconfigure(0, weight=1)
        center.grid_rowconfigure(3, weight=1)

        self.tabs = ctk.CTkTabview(
            center, height=262, fg_color=BG_CARD, corner_radius=14, border_width=1, border_color=BORDER_COLOR,
            segmented_button_fg_color=BG_INPUT, segmented_button_selected_color=ACCENT,
            segmented_button_selected_hover_color=ACCENT_HOVER, segmented_button_unselected_color=BG_INPUT,
            segmented_button_unselected_hover_color=BTN_NEUTRAL, text_color=TEXT_MAIN,
        )
        self.tabs.grid(row=0, column=0, sticky="ew")
        self._build_tab_hook(self.tabs.add("Gancho"))
        self._build_tab_arrow(self.tabs.add("Seta"))
        self._build_tab_output(self.tabs.add("Saída"))

        # Barra de ação
        bar = self._card(center)
        bar.grid(row=1, column=0, sticky="ew", pady=(10, 0))
        self.btn_generate = ctk.CTkButton(bar, text="⚡ Gerar variações", width=140, height=34, corner_radius=8,
                                          fg_color=ACCENT, hover_color=ACCENT_HOVER,
                                          font=ctk.CTkFont(size=12, weight="bold"), command=self.generate_combinations)
        self.btn_generate.pack(side="left", padx=(12, 10), pady=10)
        self.lbl_slider = ctk.CTkLabel(bar, text="Lote: 0", text_color=TEXT_MUTED, width=64, anchor="w",
                                       font=ctk.CTkFont(size=12, weight="bold"))
        self.lbl_slider.pack(side="left")
        self.btn_cancel = ctk.CTkButton(bar, text="Cancelar", width=84, height=34, corner_radius=8, fg_color=DANGER_BG,
                                        hover_color=DANGER, text_color=DANGER_TX, state="disabled",
                                        font=ctk.CTkFont(size=12, weight="bold"), command=self.cancel_render)
        self.btn_cancel.pack(side="right", padx=(8, 12), pady=10)
        self.btn_download_batch = ctk.CTkButton(bar, text="📥 Renderizar lote", width=150, height=34, corner_radius=8,
                                                fg_color=BTN_NEUTRAL, hover_color=SUCCESS_HOVER, state="disabled",
                                                font=ctk.CTkFont(size=12, weight="bold"), command=self.download_batch)
        self.btn_download_batch.pack(side="right", pady=10)
        self.slider_batch = ctk.CTkSlider(bar, from_=1, to=120, number_of_steps=119, height=16, progress_color=ACCENT,
                                          button_color=TEXT_MAIN, button_hover_color=ACCENT_SOFT, state="disabled",
                                          command=self.update_slider_label)
        self.slider_batch.set(120)
        self.slider_batch.pack(side="left", fill="x", expand=True, padx=12)

        # Progresso geral
        prog = ctk.CTkFrame(center, fg_color="transparent")
        prog.grid(row=2, column=0, sticky="ew", pady=(10, 4))
        prog.grid_columnconfigure(0, weight=1)
        self.bar_overall = ctk.CTkProgressBar(prog, height=10, corner_radius=5, progress_color=SUCCESS, fg_color=BORDER_COLOR)
        self.bar_overall.grid(row=0, column=0, sticky="ew")
        self.bar_overall.set(0)
        self.lbl_overall = ctk.CTkLabel(prog, text="Gere as variações para começar.", anchor="w",
                                        font=ctk.CTkFont(size=11), text_color=TEXT_MUTED)
        self.lbl_overall.grid(row=1, column=0, sticky="w", pady=(4, 0))

        # Fila
        queue_card = self._card(center)
        queue_card.grid(row=3, column=0, sticky="nsew", pady=(4, 0))
        queue_card.grid_columnconfigure(0, weight=1)
        queue_card.grid_rowconfigure(1, weight=1)

        qtop = ctk.CTkFrame(queue_card, fg_color="transparent")
        qtop.grid(row=0, column=0, columnspan=2, sticky="ew", padx=12, pady=(10, 6))
        self.seg_filter = ctk.CTkSegmentedButton(
            qtop, values=["Todos", "Na fila", "Prontos", "Falhas"], command=self.set_filter, height=28,
            fg_color=BG_INPUT, selected_color=ACCENT, selected_hover_color=ACCENT_HOVER,
            unselected_color=BG_INPUT, unselected_hover_color=BTN_NEUTRAL, font=ctk.CTkFont(size=11, weight="bold"))
        self.seg_filter.set("Todos")
        self.seg_filter.pack(side="left")
        ctk.CTkButton(qtop, text="Abrir pasta", width=92, height=28, corner_radius=8, fg_color=BTN_NEUTRAL,
                      hover_color=BTN_HOVER, font=ctk.CTkFont(size=11, weight="bold"),
                      command=self.open_output_folder).pack(side="right")
        self.btn_render_sel = ctk.CTkButton(qtop, text="Renderizar selecionados", width=160, height=28, corner_radius=8,
                                            fg_color=BTN_NEUTRAL, hover_color=ACCENT, state="disabled",
                                            font=ctk.CTkFont(size=11, weight="bold"), command=self.render_selected)
        self.btn_render_sel.pack(side="right", padx=8)

        cols = ("id", "ordem", "gancho", "status", "prog")
        self.tree = ttk.Treeview(queue_card, columns=cols, show="headings", style="Dash.Treeview", selectmode="extended")
        for c, title, width, anchor in (("id", "#", 60, "w"), ("ordem", "Ordem dos takes", 190, "w"),
                                        ("gancho", "Gancho", 80, "w"), ("status", "Status", 90, "w"),
                                        ("prog", "Progresso", 170, "w")):
            self.tree.heading(c, text=title, anchor="w")
            self.tree.column(c, width=width, anchor=anchor, stretch=(c == "ordem"))
        self.tree.tag_configure("queue", foreground=TEXT_MUTED)
        self.tree.tag_configure("run", foreground=ACCENT_SOFT)
        self.tree.tag_configure("done", foreground=OK_TX)
        self.tree.tag_configure("fail", foreground=DANGER_TX)
        self.tree.tag_configure("cancel", foreground=WARN)
        self.tree.grid(row=1, column=0, sticky="nsew", padx=(12, 0), pady=(0, 12))
        sb = ctk.CTkScrollbar(queue_card, command=self.tree.yview, fg_color="transparent")
        sb.grid(row=1, column=1, sticky="ns", padx=(2, 8), pady=(0, 12))
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.bind("<Double-1>", self._on_tree_double)
        self.tree.bind("<<TreeviewSelect>>", lambda e: self._update_sel_button())
        self.tree.bind("<Button-3>", self._on_tree_menu)
        self.tree.bind("<Button-2>", self._on_tree_menu)
        self.menu = tk.Menu(self, tearoff=0, bg=BG_CARD, fg=TEXT_MAIN, activebackground=ACCENT, bd=0)
        self.menu.add_command(label="Renderizar", command=self.render_selected)
        self.menu.add_command(label="Abrir vídeo", command=self.open_selected_video)
        self.menu.add_command(label="Mostrar na pasta", command=self.open_output_folder)
        self.menu.add_command(label="Ver erro", command=self.show_selected_error)

    def _slider(self, parent, row, col, key, label, lo, hi, init, fmt, color):
        f = ctk.CTkFrame(parent, fg_color="transparent")
        f.grid(row=row, column=col, sticky="ew", padx=6, pady=3)
        f.grid_columnconfigure(1, weight=1)
        ctk.CTkLabel(f, text=label, width=64, anchor="w", font=ctk.CTkFont(size=12), text_color=TEXT_MUTED).grid(row=0, column=0)
        val = ctk.CTkLabel(f, text=fmt(init), width=46, anchor="e", font=ctk.CTkFont(size=12, weight="bold"),
                           text_color=color)
        sl = ctk.CTkSlider(f, from_=lo, to=hi, number_of_steps=int(hi - lo), height=14, progress_color=color,
                           button_color=TEXT_MAIN, command=lambda v, k=key: self._on_slider(k, v))
        sl.set(init)
        sl.grid(row=0, column=1, sticky="ew", padx=8)
        val.grid(row=0, column=2)
        self.sliders[key] = (sl, val, fmt)

    def _on_slider(self, key, value):
        sl, val, fmt = self.sliders[key]
        val.configure(text=fmt(value))
        self.schedule_preview()

    def set_slider(self, key, value):
        sl, val, fmt = self.sliders[key]
        lo, hi = sl.cget("from_"), sl.cget("to")
        value = max(lo, min(hi, value))
        sl.set(value)
        val.configure(text=fmt(value))

    def _build_tab_hook(self, tab):
        self.sliders = {}
        tab.grid_columnconfigure(0, weight=1)
        tab.grid_columnconfigure(1, weight=1)

        row = ctk.CTkFrame(tab, fg_color="transparent")
        row.grid(row=0, column=0, columnspan=2, sticky="ew", pady=(0, 4))
        self.switch_hooks = ctk.CTkSwitch(row, text="Texto na tela", font=ctk.CTkFont(size=12, weight="bold"),
                                          text_color=TEXT_MAIN, switch_width=34, switch_height=18,
                                          progress_color=SUCCESS, command=self.schedule_preview)
        self.switch_hooks.select()
        self.switch_hooks.pack(side="left", padx=(4, 12))
        self.font_selector = ctk.CTkOptionMenu(
            row, values=["TikTok Sans Bold (.TTF)", "Poppins Bold (Idêntica)", "Poppins SemiBold"], width=170, height=28,
            corner_radius=8, fg_color=BTN_NEUTRAL, button_color=BTN_HOVER, button_hover_color=ACCENT,
            font=ctk.CTkFont(size=11, weight="bold"), command=lambda _: self.schedule_preview())
        self.font_selector.set("TikTok Sans Bold (.TTF)" if self.custom_font_path else "Poppins Bold (Idêntica)")
        self.font_selector.pack(side="left", padx=(0, 6))
        txt = f"✓ {os.path.basename(self.custom_font_path)[:9]}" if self.custom_font_path else "Carregar .TTF"
        self.btn_custom_font = ctk.CTkButton(
            row, text=txt, width=96, height=28, corner_radius=8, fg_color=OK_BG if self.custom_font_path else BTN_NEUTRAL,
            text_color=OK_TX if self.custom_font_path else TEXT_MAIN, hover_color=BTN_HOVER,
            font=ctk.CTkFont(size=11, weight="bold"), command=self.select_custom_font)
        self.btn_custom_font.pack(side="left")
        self.style_selector = ctk.CTkOptionMenu(
            row, values=["Contorno Preto (Sem Fundo)", "Caixa Escura (Com Fundo)"], width=190, height=28, corner_radius=8,
            fg_color=BTN_NEUTRAL, button_color=BTN_HOVER, button_hover_color=ACCENT,
            font=ctk.CTkFont(size=11, weight="bold"), command=lambda _: self.schedule_preview())
        self.style_selector.set("Contorno Preto (Sem Fundo)")
        self.style_selector.pack(side="right")

        ctk.CTkLabel(tab, text="Um gancho por linha. Cada vídeo usa um deles, em sequência.", anchor="w",
                     font=ctk.CTkFont(size=11), text_color=TEXT_MUTED).grid(row=1, column=0, columnspan=2, sticky="w", padx=4)
        self.textbox_hooks = ctk.CTkTextbox(tab, height=78, corner_radius=8, fg_color=BG_INPUT, border_width=1,
                                            border_color=BORDER_COLOR, text_color=TEXT_MAIN, font=ctk.CTkFont(size=12))
        self.textbox_hooks.grid(row=2, column=0, columnspan=2, sticky="ew", padx=2, pady=(2, 6))
        self.textbox_hooks.insert(
            "1.0",
            "POV: Seu estoque de regatas está completo\n"
            "NEM ACREDITO que achei esse modelo nesse valor\n"
            "O tecido canelado que modela o corpo sem marcar nada\n"
            "Cansada de roupa que fica descendo? Olha esse caimento\n"
            "A peça coringa de moda feminina que esgota toda semana")
        self.textbox_hooks.bind("<KeyRelease>", lambda e: self._on_hooks_changed())

        px = lambda v: f"{int(round(v))}px"
        pc = lambda v: f"{int(round(v))}%"
        self._slider(tab, 3, 0, "font", "Tamanho", 30, 76, 56, px, ACCENT)
        self._slider(tab, 3, 1, "width", "Largura", 65, 96, 90, pc, SUCCESS)
        self._slider(tab, 4, 0, "stroke", "Contorno", 2, 8, 4, px, ACCENT)
        self._slider(tab, 4, 1, "texty", "Altura", 15, 55, 36, pc, ACCENT)

    def _build_tab_arrow(self, tab):
        tab.grid_columnconfigure(0, weight=1)
        tab.grid_columnconfigure(1, weight=1)
        row = ctk.CTkFrame(tab, fg_color="transparent")
        row.grid(row=0, column=0, columnspan=2, sticky="ew", pady=(0, 8))
        self.switch_arrow = ctk.CTkSwitch(row, text="Seta no carrinho", font=ctk.CTkFont(size=12, weight="bold"),
                                          text_color=TEXT_MAIN, switch_width=34, switch_height=18,
                                          progress_color=ORANGE, command=self.schedule_preview)
        self.switch_arrow.select()
        self.switch_arrow.pack(side="left", padx=(4, 14))
        self.arrow_anim_selector = ctk.CTkOptionMenu(
            row, values=["Balançando (Bounce)", "Balançando + Piscando", "Piscando Rápido"], width=170, height=28,
            corner_radius=8, fg_color=BTN_NEUTRAL, button_color=BTN_HOVER, button_hover_color=ORANGE,
            font=ctk.CTkFont(size=11, weight="bold"), command=lambda _: self.schedule_preview())
        self.arrow_anim_selector.set("Balançando (Bounce)")
        self.arrow_anim_selector.pack(side="left", padx=4)
        self.arrow_style_selector = ctk.CTkOptionMenu(
            row, values=["Seta Laranja Shop", "Seta Amarela Viral", "Seta Branca Clean", "Imagem Customizada"],
            width=160, height=28, corner_radius=8, fg_color=BTN_NEUTRAL, button_color=BTN_HOVER,
            button_hover_color=ORANGE, font=ctk.CTkFont(size=11, weight="bold"),
            command=lambda _: self.schedule_preview())
        self.arrow_style_selector.set("Seta Laranja Shop")
        self.arrow_style_selector.pack(side="left", padx=4)
        self.btn_custom_arrow = ctk.CTkButton(row, text="🏹 Abrir PNG/GIF", width=118, height=28, corner_radius=8,
                                              fg_color=BTN_NEUTRAL, hover_color=BTN_HOVER,
                                              font=ctk.CTkFont(size=11, weight="bold"), command=self.select_custom_arrow)
        self.btn_custom_arrow.pack(side="left", padx=4)

        pc = lambda v: f"{int(round(v))}%"
        self._slider(tab, 1, 0, "arrow_x", "Posição X", 2, 45, 7, pc, ORANGE_SOFT)
        self._slider(tab, 1, 1, "arrow_y", "Posição Y", 50, 82, 68, pc, ORANGE_SOFT)
        ctk.CTkLabel(tab, text="Dica: clique ou arraste na prévia ao lado para posicionar a seta.", anchor="w",
                     font=ctk.CTkFont(size=11), text_color=TEXT_MUTED).grid(row=2, column=0, columnspan=2, sticky="w",
                                                                           padx=6, pady=(10, 0))

    def _build_tab_output(self, tab):
        tab.grid_columnconfigure(1, weight=1)

        def label(r, text):
            ctk.CTkLabel(tab, text=text, anchor="w", font=ctk.CTkFont(size=12), text_color=TEXT_MUTED).grid(
                row=r, column=0, sticky="w", padx=(6, 14), pady=5)

        label(0, "Pasta de destino")
        r0 = ctk.CTkFrame(tab, fg_color="transparent")
        r0.grid(row=0, column=1, sticky="ew")
        self.btn_folder = ctk.CTkButton(r0, text="📁 Escolher pasta", width=150, height=28, corner_radius=8,
                                        fg_color=BTN_NEUTRAL, hover_color=BTN_HOVER,
                                        font=ctk.CTkFont(size=11, weight="bold"), command=self.select_folder)
        self.btn_folder.pack(side="left")
        self.lbl_folder = ctk.CTkLabel(r0, text="Nenhuma pasta escolhida", anchor="w", font=ctk.CTkFont(size=11),
                                       text_color=TEXT_MUTED)
        self.lbl_folder.pack(side="left", padx=10)

        label(1, "Velocidade")
        self.speed_selector = ctk.CTkOptionMenu(tab, values=list(SPEEDS.keys()), width=200, height=28, corner_radius=8,
                                                fg_color=BTN_NEUTRAL, button_color=BTN_HOVER, button_hover_color=ACCENT,
                                                font=ctk.CTkFont(size=11, weight="bold"))
        self.speed_selector.set("Rápido (recomendado)")
        self.speed_selector.grid(row=1, column=1, sticky="w")

        label(2, "Vídeos ao mesmo tempo")
        self.workers_selector = ctk.CTkOptionMenu(tab, values=["Automático", "1", "2", "3", "4"], width=200, height=28,
                                                  corner_radius=8, fg_color=BTN_NEUTRAL, button_color=BTN_HOVER,
                                                  button_hover_color=ACCENT, font=ctk.CTkFont(size=11, weight="bold"))
        self.workers_selector.set("Automático")
        self.workers_selector.grid(row=2, column=1, sticky="w")

        label(3, "Codificador")
        r3 = ctk.CTkFrame(tab, fg_color="transparent")
        r3.grid(row=3, column=1, sticky="w")
        self.encoder_selector = ctk.CTkOptionMenu(r3, values=["Automático (GPU se houver)", "Somente CPU (x264)"],
                                                  width=200, height=28, corner_radius=8, fg_color=BTN_NEUTRAL,
                                                  button_color=BTN_HOVER, button_hover_color=ACCENT,
                                                  font=ctk.CTkFont(size=11, weight="bold"),
                                                  command=lambda _: self._update_encoder_badge())
        self.encoder_selector.set("Automático (GPU se houver)")
        self.encoder_selector.pack(side="left")
        self.lbl_encoder_hint = ctk.CTkLabel(r3, text="", font=ctk.CTkFont(size=11), text_color=TEXT_MUTED)
        self.lbl_encoder_hint.pack(side="left", padx=10)

        label(4, "Ordem")
        self.switch_viral = ctk.CTkSwitch(tab, text="Take 1 sempre na 2ª posição", font=ctk.CTkFont(size=12, weight="bold"),
                                          text_color=TEXT_MAIN, switch_width=34, switch_height=18, progress_color=ACCENT)
        self.switch_viral.grid(row=4, column=1, sticky="w")

    # --- Coluna 3: prévia ---
    def _build_preview_column(self, body):
        card = self._card(body, width=272)
        card.grid(row=0, column=2, sticky="ns", padx=(12, 0))
        card.pack_propagate(False)
        card.grid_propagate(False)

        ctk.CTkLabel(card, text="Prévia ao vivo", font=ctk.CTkFont(size=14, weight="bold"),
                     text_color=TEXT_MAIN).pack(pady=(12, 6))
        self.preview_label = ctk.CTkLabel(card, text="", width=PV_W, height=PV_H, fg_color=BTN_NEUTRAL, corner_radius=10)
        self.preview_label.pack(padx=18, pady=2)
        self.preview_label.bind("<Button-1>", self._preview_pointer)
        self.preview_label.bind("<B1-Motion>", self._preview_pointer)

        nav = ctk.CTkFrame(card, fg_color="transparent")
        nav.pack(fill="x", padx=18, pady=(8, 2))
        ctk.CTkButton(nav, text="◀", width=30, height=26, corner_radius=8, fg_color=BTN_NEUTRAL, hover_color=BTN_HOVER,
                      command=lambda: self._step_hook(-1)).pack(side="left")
        ctk.CTkButton(nav, text="▶", width=30, height=26, corner_radius=8, fg_color=BTN_NEUTRAL, hover_color=BTN_HOVER,
                      command=lambda: self._step_hook(1)).pack(side="right")
        self.lbl_hook_nav = ctk.CTkLabel(nav, text="Gancho 1 de 5", font=ctk.CTkFont(size=12), text_color=TEXT_MUTED)
        self.lbl_hook_nav.pack(expand=True)

        ctk.CTkButton(card, text="🔍 Ampliar prévia", height=30, corner_radius=8, fg_color=BTN_NEUTRAL,
                      hover_color=BTN_HOVER, font=ctk.CTkFont(size=12, weight="bold"),
                      command=self.open_preview_in_system_viewer).pack(fill="x", padx=18, pady=(8, 4))
        self.btn_test = ctk.CTkButton(card, text="▶ Vídeo teste (2s)", height=32, corner_radius=8, fg_color=ACCENT,
                                      hover_color=ACCENT_HOVER, font=ctk.CTkFont(size=12, weight="bold"),
                                      command=self.open_quick_video_test)
        self.btn_test.pack(fill="x", padx=18, pady=4)

    # ───────────── estado dos takes / áudio / pastas ─────────────
    def select_file(self, index):
        path = filedialog.askopenfilename(title=f"Selecione o Take {index}",
                                          filetypes=[("Vídeos", "*.mp4 *.mov *.avi *.mkv *.webm")])
        if path:
            self.set_take(index, path)

    def select_many(self):
        paths = filedialog.askopenfilenames(title="Selecione até 5 vídeos (serão os takes 1 a 5, em ordem alfabética)",
                                            filetypes=[("Vídeos", "*.mp4 *.mov *.avi *.mkv *.webm")])
        for i, p in enumerate(sorted(paths)[:5], start=1):
            self.set_take(i, p)

    def set_take(self, index, path):
        self.files[index] = path
        w = self.take_widgets[index]
        short = os.path.basename(path)
        w["name"].configure(text=short if len(short) <= 26 else short[:25] + "…", text_color=TEXT_MAIN)
        w["meta"].configure(text="Lendo vídeo...", text_color=TEXT_MUTED)
        self.update_chips()
        threading.Thread(target=self._load_take_work, args=(index, path), daemon=True).start()

    def _load_take_work(self, i, path):
        info = probe_media(path)
        frame = None
        tmp = os.path.join(self.tmp_dir, f"frame_{i}_{os.getpid()}.png")
        try:
            ss = "0.5" if info and info["duration"] > 1 else "0"
            subprocess.run(["ffmpeg", "-y", "-ss", ss, "-i", path, "-frames:v", "1", "-vf",
                            "scale=540:960:force_original_aspect_ratio=increase,crop=540:960", tmp],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, **NO_WINDOW)
            if os.path.exists(tmp):
                frame = Image.open(tmp).convert("RGB")
                frame.load()
                os.remove(tmp)
        except Exception:
            pass
        self.ui_q.put(lambda: self._take_loaded(i, path, info, frame))

    def _take_loaded(self, i, path, info, frame):
        if self.files.get(i) != path:
            return
        self.take_info[i] = info
        if frame is not None:
            self.take_frames[i] = frame
            thumb = frame.resize((34, 56), LANCZOS)
            img = ctk.CTkImage(thumb, size=(34, 56))
            self.take_widgets[i]["thumb"].configure(image=img, text="")
            self.take_widgets[i]["_img"] = img
        self._pv_bg_cache.clear()
        self._refresh_take_meta()
        self.schedule_preview()
        self.update_chips()

    def _refresh_take_meta(self):
        ref = next((self.take_info[i] for i in range(1, 6) if self.take_info.get(i) and self.take_info[i]["w"]), None)
        for i in range(1, 6):
            info = self.take_info.get(i)
            meta = self.take_widgets[i]["meta"]
            if not self.files[i]:
                continue
            if not info:
                meta.configure(text="Não consegui ler o vídeo", text_color=DANGER_TX)
                continue
            txt = f"{fmt_time(info['duration'])}  ·  {info['w']}×{info['h']}" if info["w"] else fmt_time(info["duration"])
            diff = ref and info["w"] and (info["w"], info["h"]) != (ref["w"], ref["h"])
            meta.configure(text=txt + ("  (resolução diferente)" if diff else ""),
                           text_color=WARN if diff else TEXT_MUTED)

    def clear_take(self, i):
        self.files[i] = None
        self.take_info.pop(i, None)
        self.take_frames.pop(i, None)
        w = self.take_widgets[i]
        w["name"].configure(text=f"Take {i}", text_color=TEXT_MAIN)
        w["meta"].configure(text="Escolher vídeo", text_color=TEXT_MUTED)
        w["thumb"].configure(image=self.blank_img, text="＋")
        self._pv_bg_cache.clear()
        self._refresh_take_meta()
        self.schedule_preview()
        self.update_chips()

    def select_audio(self):
        path = filedialog.askopenfilename(title="Selecione o áudio", filetypes=[("Áudios", "*.mp3 *.wav *.m4a *.aac *.ogg")])
        if path:
            self.set_audio(path)

    def set_audio(self, path):
        self.audio_file = path
        name = os.path.basename(path)
        self.lbl_audio.configure(text=name if len(name) <= 22 else name[:21] + "…", text_color=OK_TX)
        self.btn_audio.configure(fg_color=OK_BG, text_color=OK_TX)
        self.audio_dur = 0.0

        def work():
            info = probe_media(path)
            self.audio_dur = info["duration"] if info else 0.0
        threading.Thread(target=work, daemon=True).start()

    def clear_audio(self):
        self.audio_file = None
        self.audio_dur = 0.0
        self.lbl_audio.configure(text="Mantém o som dos takes", text_color=TEXT_MUTED)
        self.btn_audio.configure(fg_color=BTN_NEUTRAL, text_color=TEXT_MAIN)

    def select_custom_font(self):
        path = filedialog.askopenfilename(title="Selecione a fonte (.ttf ou .otf)", filetypes=[("Fontes", "*.ttf *.otf")])
        if not path:
            return
        dest = os.path.join(self.assets_dir, os.path.basename(path))
        try:
            shutil.copy2(path, dest)
            self.custom_font_path = dest
        except Exception:
            self.custom_font_path = path
        try:
            with open(self.saved_font_config, "w", encoding="utf-8") as f:
                f.write(self.custom_font_path)
        except Exception:
            pass
        self.btn_custom_font.configure(text=f"✓ {os.path.basename(path)[:9]}", fg_color=OK_BG, text_color=OK_TX)
        self.font_selector.set("TikTok Sans Bold (.TTF)")
        self.schedule_preview()

    def select_custom_arrow(self):
        path = filedialog.askopenfilename(title="Selecione uma seta (.png, .gif ou .webp)",
                                          filetypes=[("Imagens/GIF", "*.png *.gif *.webp")])
        if path:
            self.custom_arrow_path = path
            self.btn_custom_arrow.configure(text=f"✓ {os.path.basename(path)[:10]}", fg_color=OK_BG, text_color=OK_TX)
            self.arrow_style_selector.set("Imagem Customizada")
            self.schedule_preview()

    def select_folder(self):
        folder = filedialog.askdirectory(title="Selecione a pasta de destino")
        if folder:
            self.set_output_folder(folder)

    def set_output_folder(self, folder):
        self.output_folder = folder
        name = os.path.basename(folder) or folder
        self.lbl_folder.configure(text=name if len(name) <= 40 else name[:39] + "…", text_color=OK_TX)
        self.btn_folder.configure(fg_color=OK_BG, text_color=OK_TX)

    def open_output_folder(self):
        if self.output_folder and os.path.isdir(self.output_folder):
            open_path(self.output_folder)
        else:
            messagebox.showinfo("Pasta de destino", "Escolha primeiro a pasta de destino na aba Saída.")

    # ───────────── snapshot das configurações (thread-safe) ─────────────
    def hooks_list(self):
        return [h.strip() for h in self.textbox_hooks.get("1.0", "end").strip().splitlines() if h.strip()]

    def out_wh(self):
        for i in range(1, 6):
            info = self.take_info.get(i)
            if info and info["w"]:
                return max(2, info["w"] - 2 * CROP_PX), max(2, info["h"] - 2 * CROP_PX)
        return 1080 - 2 * CROP_PX, 1920 - 2 * CROP_PX

    def snapshot(self):
        out_w, out_h = self.out_wh()
        arrow_path = self.get_arrow_image_path()
        arrow_px = max(8, int(round(ARROW_BASE_PX * out_w / 1080.0)))
        use_hw = self.hw_encoder and self.encoder_selector.get().startswith("Auto")
        workers = self.workers_selector.get()
        if workers == "Automático":
            workers = 2 if use_hw else max(1, min(4, (os.cpu_count() or 4) // 3))
        else:
            workers = int(workers)
        return {
            "hooks_on": bool(self.switch_hooks.get()),
            "hooks": self.hooks_list(),
            "font_path": self.get_resolved_font_path(),
            "style": self.style_selector.get(),
            "font_size": int(self.sliders["font"][0].get()),
            "stroke": int(self.sliders["stroke"][0].get()),
            "max_w": self.sliders["width"][0].get() / 100.0,
            "text_y": self.sliders["texty"][0].get() / 100.0,
            "arrow_on": bool(self.switch_arrow.get()),
            "arrow_path": arrow_path,
            "arrow_png": prepare_arrow_png(arrow_path, arrow_px, self.arrow_cache),
            "arrow_px": arrow_px,
            "arrow_anim": self.arrow_anim_selector.get(),
            "arrow_x": self.sliders["arrow_x"][0].get() / 100.0,
            "arrow_y": self.sliders["arrow_y"][0].get() / 100.0,
            "audio": self.audio_file,
            "audio_dur": self.audio_dur,
            "out_w": out_w,
            "out_h": out_h,
            "preset": SPEEDS.get(self.speed_selector.get(), "veryfast"),
            "hw": (self.hw_encoder[1], self.hw_encoder[2]) if use_hw else None,
            "workers": workers,
        }

    # ───────────── prévia ─────────────
    def _on_hooks_changed(self):
        self.schedule_preview()

    def _step_hook(self, delta):
        n = len(self.hooks_list())
        if n:
            self.hook_idx = (self.hook_idx + delta) % n
            self.schedule_preview()

    def schedule_preview(self, *_):
        if self._pv_job is not None:
            try:
                self.after_cancel(self._pv_job)
            except Exception:
                pass
        self._pv_job = self.after(40, self.refresh_embedded_preview)

    def get_preview_background(self, cw, ch):
        first = next((i for i in range(1, 6) if i in self.take_frames), None)
        key = (first, cw, ch)
        if key in self._pv_bg_cache:
            return self._pv_bg_cache[key].copy()
        if first is not None:
            bg = self.take_frames[first].resize((cw, ch), LANCZOS).convert("RGBA")
        else:
            bg = Image.new("RGBA", (cw, ch), (42, 50, 66, 255))
            d = ImageDraw.Draw(bg)
            step = max(8, cw // 9)
            for y in range(0, ch, step):
                d.line([(0, y), (cw, y)], fill=(58, 68, 88, 255), width=1)
            for x in range(0, cw, step):
                d.line([(x, 0), (x, ch)], fill=(58, 68, 88, 255), width=1)
        self._pv_bg_cache[key] = bg
        return bg.copy()

    def build_preview_layers(self, cw, ch):
        """Devolve (fundo_com_texto_e_mock, sprite_da_seta, (ax, ay), cfg)."""
        cfg = self.snapshot()
        k = cw / 288.0
        bg = self.get_preview_background(cw, ch)
        hooks = cfg["hooks"]
        if cfg["hooks_on"] and hooks:
            text = hooks[self.hook_idx % len(hooks)]
            bg.alpha_composite(render_hook_overlay(cfg, text, cw, ch, False))

        d = ImageDraw.Draw(bg)
        f10 = load_font(cfg["font_path"], max(7, int(10 * k)))
        f8 = load_font(cfg["font_path"], max(6, int(8 * k)))
        top = int(ch * 0.79)
        bot = top + int(24 * k)
        d.rectangle([int(18 * k), top, int(155 * k), bot], fill=(28, 28, 28, 225), outline=(90, 90, 90, 255), width=1)
        d.rectangle([int(21 * k), top + int(3 * k), int(40 * k), bot - int(3 * k)], fill=(255, 85, 0, 255))
        d.text((int(45 * k), top + int(6 * k)), "Loja • COMPRE AQUI", font=f10, fill=(255, 255, 255, 255))
        d.text((int(18 * k), bot + int(6 * k)), "@mulheremestilo • Há 8h", font=f10, fill=(240, 240, 240, 255))
        d.rectangle([int(18 * k), bot + int(22 * k), int(148 * k), bot + int(36 * k)], fill=(35, 35, 35, 210))
        d.text((int(22 * k), bot + int(24 * k)), "Contém mídia gerada por IA", font=f8, fill=(200, 200, 200, 255))

        sprite, pos = None, (0, 0)
        if cfg["arrow_on"] and os.path.exists(cfg["arrow_path"]):
            try:
                px = max(8, int(round(ARROW_BASE_PX * cw / 1080.0)))
                sprite = Image.open(cfg["arrow_path"]).convert("RGBA").resize((px, px), LANCZOS)
                pos = (int(cw * cfg["arrow_x"]), int(ch * cfg["arrow_y"]))
            except Exception:
                sprite = None
        return bg, sprite, pos, cfg

    def refresh_embedded_preview(self):
        self._pv_job = None
        try:
            bg, sprite, pos, cfg = self.build_preview_layers(PV_W, PV_H)
        except Exception:
            traceback.print_exc()
            return
        n = len(cfg["hooks"])
        if n:
            self.hook_idx %= n
        self.lbl_hook_nav.configure(text=f"Gancho {self.hook_idx + 1} de {n}" if n else "Sem ganchos")
        self._pv = {"base": bg, "sprite": sprite, "pos": pos, "mode": cfg["arrow_anim"], "amp": ARROW_AMP_PX * PV_W / 1080.0}
        self._draw_preview_frame()

    def _arrow_state(self, t):
        """Mesma matemática do ffmpeg: balanço = amp*sin(t*9); piscar = enable por mod(t, período)."""
        pv = self._pv
        mode = pv["mode"]
        dy = 0.0 if "Piscando Rápido" in mode else pv["amp"] * math.sin(t * 9)
        visible = True
        if "Balançando + Piscando" in mode:
            visible = (t % 0.75) > 0.18
        elif "Piscando Rápido" in mode:
            visible = (t % 0.55) > 0.20
        return dy, visible

    def _draw_preview_frame(self):
        pv = self._pv
        if not pv:
            return
        frame = pv["base"]
        if pv["sprite"] is not None:
            dy, visible = self._arrow_state(time.time() - self._anim_t0)
            frame = frame.copy()
            if visible:
                x, y = pv["pos"]
                frame.paste(pv["sprite"], (int(x), int(y + dy)), pv["sprite"])
        rgb = frame.convert("RGB")
        self._pv_img = ctk.CTkImage(light_image=rgb, dark_image=rgb, size=(PV_W, PV_H))
        self.preview_label.configure(image=self._pv_img)

    def _anim_tick(self):
        try:
            if self._pv and self._pv["sprite"] is not None:
                self._draw_preview_frame()
        except Exception:
            pass
        self.after(260 if self.rendering else 90, self._anim_tick)

    def _preview_pointer(self, event):
        """Clique/arraste na prévia move a seta."""
        pv = self._pv
        if not pv or pv["sprite"] is None:
            return
        sx, sy = pv["sprite"].size
        self.set_slider("arrow_x", (event.x - sx / 2) / PV_W * 100.0)
        self.set_slider("arrow_y", (event.y - sy / 2) / PV_H * 100.0)
        self.schedule_preview()

    def open_preview_in_system_viewer(self):
        try:
            bg, sprite, pos, cfg = self.build_preview_layers(540, 960)
            if sprite is not None:
                bg.paste(sprite, pos, sprite)
            out = os.path.join(self.assets_dir, "mira_ampliada.png")
            bg.convert("RGB").save(out, "PNG")
            open_path(out)
        except Exception as e:
            messagebox.showerror("Erro", str(e))

    def open_quick_video_test(self):
        first = next((p for p in self.files.values() if p and os.path.exists(p)), None)
        if not first:
            messagebox.showwarning("Aviso", "Selecione pelo menos o Take 1 para gerar o vídeo teste.")
            return
        if not shutil.which("ffmpeg"):
            messagebox.showerror("Erro", "FFmpeg não encontrado no sistema.")
            return
        cfg = dict(self.snapshot(), hw=None, preset="ultrafast")
        hooks = cfg["hooks"]
        text = hooks[self.hook_idx % len(hooks)] if (cfg["hooks_on"] and hooks) else ""
        self.btn_test.configure(state="disabled", text="Gerando teste...")

        def work():
            out = os.path.join(self.assets_dir, "teste_mira_2s.mp4")
            prefix = os.path.join(self.tmp_dir, "teste")
            temps, err = [], ""
            try:
                if os.path.exists(out):
                    os.remove(out)
                cmd, temps = build_command(cfg, [first], out, prefix, text, limit=2.2, with_audio=False)
                r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                                   encoding="utf-8", errors="replace", **NO_WINDOW)
                if r.returncode != 0:
                    err = "\n".join([l for l in (r.stdout or "").splitlines() if l.split("=")[0] not in PROGRESS_KEYS][-8:])
            except Exception as e:
                err = str(e)
            finally:
                for t in temps:
                    try:
                        os.remove(t)
                    except Exception:
                        pass

            def done():
                self.btn_test.configure(state="normal", text="▶ Vídeo teste (2s)")
                if os.path.exists(out) and not err:
                    open_path(out)
                else:
                    messagebox.showerror("Erro no teste", err or "Não foi possível gerar o vídeo teste.")
            self.ui_q.put(done)
        threading.Thread(target=work, daemon=True).start()

    # ───────────── matriz de variações / fila ─────────────
    def check_ffmpeg(self):
        return shutil.which("ffmpeg") is not None

    def update_slider_label(self, value):
        n = int(round(value))
        self.lbl_slider.configure(text=f"Lote: {n}")
        if self.btn_download_batch.cget("state") != "disabled" and not self.rendering:
            self.btn_download_batch.configure(text=f"📥 Renderizar ({n})")

    def generate_combinations(self):
        if self.rendering:
            return
        if not all(self.files.values()):
            messagebox.showwarning("Aviso", "Selecione todos os 5 takes antes de gerar.")
            return
        if not self.check_ffmpeg():
            messagebox.showerror("Erro", "FFmpeg não encontrado no sistema.")
            return
        sizes = {(i["w"], i["h"]) for i in self.take_info.values() if i and i["w"]}
        if len(sizes) > 1 and not messagebox.askyesno(
                "Resoluções diferentes",
                "Os takes têm resoluções diferentes e o resultado pode falhar ou ficar com tarjas.\n\nGerar mesmo assim?"):
            return

        combos = list(itertools.permutations([1, 2, 3, 4, 5]))
        if self.switch_viral.get() == 1:
            combos = [c for c in combos if c[1] == 1]
        self.combinations = combos
        self.status = {i: "queue" for i in range(len(combos))}
        self.prog_pct, self.errors, self.out_paths = {}, {}, {}
        total = len(combos)
        self.slider_batch.configure(state="normal", from_=1, to=total, number_of_steps=max(1, total - 1))
        self.slider_batch.set(total)
        self.lbl_slider.configure(text=f"Lote: {total}", text_color=TEXT_MAIN)
        self.btn_download_batch.configure(state="normal", text=f"📥 Renderizar ({total})", fg_color=SUCCESS,
                                          text_color="#052E16")
        self.bar_overall.set(0)
        self.lbl_overall.configure(text=f"{total} variações prontas para renderizar.", text_color=TEXT_MUTED)
        self.refresh_tree()
        self.update_chips()

    def _hook_label(self, idx):
        n = len(self.hooks_list())
        return f"Gancho {(idx % n) + 1}" if n else "-"

    def _progress_text(self, st, pct):
        if st == "done":
            return "▰" * 10 + " 100%"
        if st == "run":
            f = int(pct / 10)
            return "▰" * f + "▱" * (10 - f) + f" {int(pct)}%"
        return ""

    def _row_values(self, idx):
        st = self.status.get(idx, "queue")
        combo = self.combinations[idx]
        return (f"#{idx + 1:03d}", " → ".join(map(str, combo)), self._hook_label(idx), STATUS_TXT[st],
                self._progress_text(st, self.prog_pct.get(idx, 0)))

    def set_filter(self, value):
        self.filter_mode = value
        self.refresh_tree()

    def _passes_filter(self, st):
        return {"Todos": True, "Na fila": st in ("queue", "run", "cancel"), "Prontos": st == "done",
                "Falhas": st == "fail"}.get(self.filter_mode, True)

    def refresh_tree(self):
        self.tree.delete(*self.tree.get_children())
        for idx in range(len(self.combinations)):
            st = self.status.get(idx, "queue")
            if self._passes_filter(st):
                self.tree.insert("", "end", iid=str(idx), values=self._row_values(idx), tags=(st,))
        self._update_sel_button()

    def _update_sel_button(self):
        sel = self.tree.selection()
        enabled = bool(sel) and not self.rendering
        self.btn_render_sel.configure(state="normal" if enabled else "disabled",
                                      text=f"Renderizar selecionados ({len(sel)})" if sel else "Renderizar selecionados")

    def _set_status(self, idx, status, pct=None, err=None):
        self.status[idx] = status
        if pct is not None:
            self.prog_pct[idx] = pct
        if err:
            self.errors[idx] = err
        iid = str(idx)
        if self.tree.exists(iid):
            if self._passes_filter(status):
                self.tree.item(iid, values=self._row_values(idx), tags=(status,))
            else:
                self.tree.delete(iid)
        elif self._passes_filter(status) and status in ("done", "fail"):
            self.refresh_tree()
        if status in ("done", "fail", "cancel"):
            self.update_chips()

    def _post(self, idx, status, pct=None, err=None):
        self.ui_q.put(lambda: self._set_status(idx, status, pct, err))

    def _on_tree_double(self, event):
        iid = self.tree.identify_row(event.y)
        if not iid:
            return
        idx = int(iid)
        st = self.status.get(idx)
        if st == "done":
            self.open_video(idx)
        elif st == "fail" and self.errors.get(idx):
            self.show_error(idx)
        elif not self.rendering:
            self._start_render([idx], force=True)

    def _on_tree_menu(self, event):
        iid = self.tree.identify_row(event.y)
        if iid:
            if iid not in self.tree.selection():
                self.tree.selection_set(iid)
            self.menu.tk_popup(event.x_root, event.y_root)

    def selected_indices(self):
        return sorted(int(i) for i in self.tree.selection())

    def open_video(self, idx):
        path = self.out_paths.get(idx)
        if path and os.path.exists(path):
            open_path(path)
        else:
            messagebox.showinfo("Vídeo", "Esse vídeo ainda não foi renderizado.")

    def open_selected_video(self):
        sel = self.selected_indices()
        if sel:
            self.open_video(sel[0])

    def show_error(self, idx):
        messagebox.showerror(f"Erro no vídeo #{idx + 1:03d}", self.errors.get(idx, "Sem detalhes."))

    def show_selected_error(self):
        sel = self.selected_indices()
        if sel:
            if self.errors.get(sel[0]):
                self.show_error(sel[0])
            else:
                messagebox.showinfo("Erro", "Esse vídeo não tem erro registrado.")

    # ───────────── estatísticas ─────────────
    def update_chips(self):
        loaded = sum(1 for p in self.files.values() if p)
        self.chips["takes"].configure(text=f"{loaded}/5", text_color=OK_TX if loaded == 5 else TEXT_MAIN)
        self.chips["combos"].configure(text=str(len(self.combinations)))
        done = sum(1 for s in self.status.values() if s == "done")
        self.chips["done"].configure(text=f"{done}/{len(self.combinations)}")

    def _tick_stats(self):
        try:
            if self.rendering and self.batch_idx:
                total = len(self.batch_idx)
                frac = sum(self.job_prog.get(i, 0.0) for i in self.batch_idx) / total
                done = sum(1 for i in self.batch_idx if self.status.get(i) == "done")
                elapsed = time.time() - self.batch_start
                self.bar_overall.set(min(1.0, frac))
                eta = "calculando"
                if frac > 0.03:
                    eta = fmt_time(elapsed / frac - elapsed)
                    self.chips["eta"].configure(text=eta)
                self.lbl_overall.configure(
                    text=f"{done} de {total} prontos  ·  {int(frac * 100)}%  ·  decorrido {fmt_time(elapsed)}  ·  restante {eta}",
                    text_color=TEXT_MAIN)
        except Exception:
            pass
        self.after(500, self._tick_stats)

    # ───────────── renderização ─────────────
    def download_batch(self):
        if not self.combinations or self.rendering:
            return
        limit = int(round(self.slider_batch.get()))
        self._start_render(list(range(limit)), force=False)

    def render_selected(self):
        sel = self.selected_indices()
        if sel and not self.rendering:
            self._start_render(sel, force=True)

    def _start_render(self, indices, force):
        if self.rendering:
            return
        if not self.check_ffmpeg():
            messagebox.showerror("Erro", "FFmpeg não encontrado no sistema.")
            return
        if not self.output_folder:
            self.select_folder()
            if not self.output_folder:
                return
        if not force:
            indices = [i for i in indices if self.status.get(i) != "done"]
        if not indices:
            self.lbl_overall.configure(text="Tudo isso já foi renderizado.", text_color=OK_TX)
            return

        cfg = self.snapshot()
        cfg.update({
            "files": dict(self.files),
            "combos": list(self.combinations),
            "out_dir": self.output_folder,
            "durs": {i: (self.take_info.get(i) or {}).get("duration", 0.0) for i in range(1, 6)},
        })
        os.makedirs(self.output_folder, exist_ok=True)

        self.cancel_event.clear()
        self.rendering = True
        self.batch_idx = list(indices)
        self.job_prog = {i: 0.0 for i in indices}
        self.batch_start = time.time()
        for i in indices:
            self.status[i] = "queue"
            self.prog_pct[i] = 0
        self.refresh_tree()
        self._set_busy(True)
        threading.Thread(target=self._batch_runner, args=(list(indices), cfg), daemon=True).start()

    def _set_busy(self, busy):
        self.btn_generate.configure(state="disabled" if busy else "normal")
        self.btn_cancel.configure(state="normal" if busy else "disabled")
        self.slider_batch.configure(state="disabled" if busy else ("normal" if self.combinations else "disabled"))
        if busy:
            self.btn_download_batch.configure(state="disabled", text="Renderizando...", fg_color=BTN_NEUTRAL,
                                              text_color=TEXT_MUTED)
        self._update_sel_button()

    def cancel_render(self):
        if not self.rendering:
            return
        self.cancel_event.set()
        self.lbl_overall.configure(text="Cancelando...", text_color=WARN)
        with self.proc_lock:
            for p in list(self.procs):
                try:
                    p.terminate()
                except Exception:
                    pass

    def _batch_runner(self, indices, cfg):
        try:
            with ThreadPoolExecutor(max_workers=max(1, cfg["workers"])) as ex:
                list(ex.map(lambda i: self._render_one(i, cfg), indices))
        except Exception:
            traceback.print_exc()
        finally:
            self.ui_q.put(self._on_batch_done)

    def _run_ffmpeg(self, cmd, total_dur, on_progress):
        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                                encoding="utf-8", errors="replace", **NO_WINDOW)
        with self.proc_lock:
            self.procs.add(proc)
        tail = []
        try:
            for line in proc.stdout:
                line = line.strip()
                if not line:
                    continue
                key, _, val = line.partition("=")
                if key in ("out_time_us", "out_time_ms"):
                    if val.lstrip("-").isdigit() and total_dur > 0:
                        on_progress(max(0.0, min(1.0, int(val) / 1e6 / total_dur)))
                elif key in PROGRESS_KEYS:
                    continue
                else:
                    tail.append(line)
                    tail = tail[-14:]
            rc = proc.wait()
        finally:
            with self.proc_lock:
                self.procs.discard(proc)
        return rc, "\n".join(tail)

    def _render_one(self, idx, cfg):
        if self.cancel_event.is_set():
            self._post(idx, "cancel")
            return
        n = idx + 1
        combo = cfg["combos"][idx]
        files = [cfg["files"][t] for t in combo]
        out_path = os.path.join(cfg["out_dir"], f"Vídeo_Blindado_{n:03d}.mp4")
        hooks = cfg["hooks"]
        hook_text = hooks[(n - 1) % len(hooks)] if (cfg["hooks_on"] and hooks) else ""
        prefix = os.path.join(self.tmp_dir, f"job{n:03d}_{threading.get_ident()}")

        total = sum(cfg["durs"].get(t, 0.0) for t in combo)
        if cfg["audio"] and cfg["audio_dur"] > 0:
            total = min(total, cfg["audio_dur"]) if total > 0 else cfg["audio_dur"]

        self._post(idx, "run", 0)
        last = {"p": -1}

        def on_progress(frac):
            self.job_prog[idx] = frac
            p = int(frac * 100)
            if p != last["p"] and (p - last["p"] >= 2 or p >= 99):
                last["p"] = p
                self._post(idx, "run", p)

        temps_all, rc, tail = [], -1, ""
        try:
            for attempt in range(2):
                use_cfg = cfg if attempt == 0 else dict(cfg, hw=None)
                cmd, temps = build_command(use_cfg, files, out_path, prefix, hook_text)
                temps_all += temps
                rc, tail = self._run_ffmpeg(cmd, total, on_progress)
                if rc == 0 or self.cancel_event.is_set() or not cfg.get("hw"):
                    break
        except Exception as e:
            rc, tail = -1, f"{e}\n{traceback.format_exc()}"
        finally:
            for t in temps_all:
                try:
                    os.remove(t)
                except Exception:
                    pass

        if rc == 0:
            self.job_prog[idx] = 1.0
            self.out_paths[idx] = out_path
            self._post(idx, "done", 100)
        elif self.cancel_event.is_set():
            try:
                if os.path.exists(out_path):
                    os.remove(out_path)
            except Exception:
                pass
            self.job_prog[idx] = 0.0
            self._post(idx, "cancel", 0)
        else:
            print(f"Erro do FFmpeg no vídeo {n}:\n{tail}")
            self.job_prog[idx] = 1.0
            self._post(idx, "fail", 0, tail or "Erro desconhecido do ffmpeg.")

    def _on_batch_done(self):
        self.rendering = False
        with self.proc_lock:
            self.procs.clear()
        total = len(self.batch_idx)
        ok = sum(1 for i in self.batch_idx if self.status.get(i) == "done")
        fail = sum(1 for i in self.batch_idx if self.status.get(i) == "fail")
        canc = sum(1 for i in self.batch_idx if self.status.get(i) == "cancel")
        elapsed = fmt_time(time.time() - self.batch_start)
        self._set_busy(False)
        self.bar_overall.set(1.0 if ok == total else (ok / total if total else 0))
        self.chips["eta"].configure(text="--")
        parts = [f"{ok} de {total} renderizados em {elapsed}"]
        if fail:
            parts.append(f"{fail} falharam (clique duas vezes na linha para ver o erro)")
        if canc:
            parts.append(f"{canc} cancelados")
        self.lbl_overall.configure(text=".  ".join(parts) + ".", text_color=OK_TX if not fail else WARN)
        remaining = sum(1 for s in self.status.values() if s != "done")
        if self.combinations:
            n = int(round(self.slider_batch.get()))
            self.btn_download_batch.configure(
                state="normal", fg_color=SUCCESS if remaining else BTN_NEUTRAL, text_color="#052E16" if remaining else TEXT_MAIN,
                text=f"📥 Renderizar ({n})" if remaining else "✓ Lote concluído")
        self.update_chips()
        try:
            self.bell()
        except Exception:
            pass

    # ───────────── configurações salvas ─────────────
    def save_settings(self):
        try:
            data = {
                "files": {str(k): v for k, v in self.files.items() if v},
                "audio": self.audio_file,
                "out": self.output_folder,
                "hooks_text": self.textbox_hooks.get("1.0", "end").strip(),
                "hooks_on": bool(self.switch_hooks.get()),
                "font_choice": self.font_selector.get(),
                "style": self.style_selector.get(),
                "sliders": {k: float(v[0].get()) for k, v in self.sliders.items()},
                "arrow_on": bool(self.switch_arrow.get()),
                "arrow_anim": self.arrow_anim_selector.get(),
                "arrow_style": self.arrow_style_selector.get(),
                "custom_arrow": self.custom_arrow_path,
                "viral": bool(self.switch_viral.get()),
                "speed": self.speed_selector.get(),
                "workers": self.workers_selector.get(),
                "encoder": self.encoder_selector.get(),
            }
            with open(self.settings_path, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
        except Exception:
            traceback.print_exc()

    def load_settings(self):
        try:
            with open(self.settings_path, "r", encoding="utf-8") as f:
                d = json.load(f)
        except Exception:
            return

        def opt(menu, value):
            if value and value in menu.cget("values"):
                menu.set(value)

        try:
            if d.get("hooks_text"):
                self.textbox_hooks.delete("1.0", "end")
                self.textbox_hooks.insert("1.0", d["hooks_text"])
            (self.switch_hooks.select if d.get("hooks_on", True) else self.switch_hooks.deselect)()
            (self.switch_arrow.select if d.get("arrow_on", True) else self.switch_arrow.deselect)()
            (self.switch_viral.select if d.get("viral") else self.switch_viral.deselect)()
            opt(self.font_selector, d.get("font_choice"))
            opt(self.style_selector, d.get("style"))
            opt(self.arrow_anim_selector, d.get("arrow_anim"))
            opt(self.speed_selector, d.get("speed"))
            opt(self.workers_selector, d.get("workers"))
            opt(self.encoder_selector, d.get("encoder"))
            for k, v in d.get("sliders", {}).items():
                if k in self.sliders:
                    self.set_slider(k, v)
            ca = d.get("custom_arrow")
            if ca and os.path.exists(ca):
                self.custom_arrow_path = ca
                self.btn_custom_arrow.configure(text=f"✓ {os.path.basename(ca)[:10]}", fg_color=OK_BG, text_color=OK_TX)
            opt(self.arrow_style_selector, d.get("arrow_style"))
            for k, p in d.get("files", {}).items():
                if os.path.exists(p):
                    self.set_take(int(k), p)
            if d.get("audio") and os.path.exists(d["audio"]):
                self.set_audio(d["audio"])
            if d.get("out") and os.path.isdir(d["out"]):
                self.set_output_folder(d["out"])
        except Exception:
            traceback.print_exc()

    def on_close(self):
        self.cancel_event.set()
        with self.proc_lock:
            for p in list(self.procs):
                try:
                    p.terminate()
                except Exception:
                    pass
        self.save_settings()
        self.destroy()


if __name__ == "__main__":
    try:
        app = VideoCombinerApp()
        app.mainloop()
    except Exception:
        err = traceback.format_exc()
        print(err)
        r = tk.Tk()
        r.withdraw()
        messagebox.showerror("Erro fatal", err[-1500:])
