# =============================================================
#   ECC CRYPTOGRAPHY LAB  -  Version Finale Corrigee
#   Chiffrement XOR + SHA256 (fonctionne sur toutes les courbes)
#   Operations manuelles avec guide pas-a-pas
#   Compatible Spyder / Python 3.x
# =============================================================

import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext
import hashlib
import random
import threading
import time
import math

# -------------------------------------------------------------
#  MATHEMATIQUES
# -------------------------------------------------------------

def mod_inverse(a, m):
    if a == 0:
        raise ZeroDivisionError("Pas d inverse pour 0")
    old_r, r = a % m, m
    old_s, s = 1, 0
    while r != 0:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_s, s = s, old_s - q * s
    if old_r != 1:
        raise ValueError("Inverse inexistant")
    return old_s % m


def is_prime(n):
    if n < 2: return False
    if n in (2, 3): return True
    if n % 2 == 0: return False
    r, d = 0, n - 1
    while d % 2 == 0:
        r += 1
        d //= 2
    for a in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]:
        if a >= n: continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1: continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1: break
        else:
            return False
    return True


# -------------------------------------------------------------
#  COURBE ELLIPTIQUE
# -------------------------------------------------------------

class EllipticCurve:
    def __init__(self, a, b, p):
        self.a = a
        self.b = b
        self.p = p
        if (4 * a**3 + 27 * b**2) % p == 0:
            raise ValueError("Courbe singuliere !")

    def is_on_curve(self, P):
        if P is None: return True
        x, y = P
        return (y*y - x*x*x - self.a*x - self.b) % self.p == 0

    def point_add(self, P, Q):
        if P is None: return Q
        if Q is None: return P
        x1, y1 = P
        x2, y2 = Q
        if x1 == x2:
            if y1 != y2 or y1 == 0: return None
            lam = (3*x1*x1 + self.a) * mod_inverse(2*y1, self.p) % self.p
        else:
            lam = (y2 - y1) * mod_inverse(x2 - x1, self.p) % self.p
        x3 = (lam*lam - x1 - x2) % self.p
        y3 = (lam*(x1 - x3) - y1) % self.p
        return (x3, y3)

    def point_neg(self, P):
        if P is None: return None
        return (P[0], (-P[1]) % self.p)

    def scalar_mult(self, k, P):
        if k < 0:
            k = -k
            P = self.point_neg(P)
        result = None
        addend = P
        while k:
            if k & 1: result = self.point_add(result, addend)
            addend = self.point_add(addend, addend)
            k >>= 1
        return result

    def get_curve_points(self):
        """Calcule tous les points - Tonelli-Shanks fonctionne pour tout premier p."""
        points = []
        for x in range(self.p):
            rhs = (x**3 + self.a*x + self.b) % self.p
            if rhs == 0:
                points.append((x, 0))
            elif pow(rhs, (self.p - 1) // 2, self.p) == 1:
                y = self._sqrt_mod(rhs, self.p)
                if y is not None and (y * y) % self.p == rhs:
                    points.append((x, y))
                    if y != 0:
                        points.append((x, self.p - y))
        return points

    def _sqrt_mod(self, n, p):
        """Racine carree modulaire - Tonelli-Shanks."""
        if n == 0:
            return 0
        if p % 4 == 3:
            return pow(n, (p + 1) // 4, p)
        # Tonelli-Shanks general (pour p≡1 mod 4 comme p=97)
        q, s = p - 1, 0
        while q % 2 == 0:
            q //= 2
            s += 1
        z = 2
        while pow(z, (p - 1) // 2, p) != p - 1:
            z += 1
        m_ts = s
        c = pow(z, q, p)
        t = pow(n, q, p)
        r = pow(n, (q + 1) // 2, p)
        while True:
            if t == 0: return 0
            if t == 1: return r
            i, temp = 1, (t * t) % p
            while temp != 1:
                temp = (temp * temp) % p
                i += 1
            b = pow(c, 1 << (m_ts - i - 1), p)
            m_ts = i
            c = (b * b) % p
            t = (t * b * b) % p
            r = (r * b) % p


# -------------------------------------------------------------
#  COURBES
# -------------------------------------------------------------

CURVES = {
    "Tiny - pedagogique (p=97)": {
        "p": 97, "a": 2, "b": 3,
        "Gx": 3, "Gy": 6, "n": 5,
        "desc": "Petite courbe pour visualisation"
    },
    "Petite - pedagogique (p=211)": {
        "p": 211, "a": 0, "b": 7,
        "Gx": 2, "Gy": 2, "n": 211,
        "desc": "Courbe pedagogique moyenne"
    },
    "secp256k1 - Bitcoin": {
        "p":  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F,
        "a":  0, "b": 7,
        "Gx": 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
        "Gy": 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8,
        "n":  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141,
        "desc": "Courbe Bitcoin et Ethereum"
    },
    "secp192r1 - NIST P-192": {
        "p":  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFFFFFFFFFFFF,
        "a":  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFFFFFFFFFFFC,
        "b":  0x64210519E59C80E70FA7E9AB72243049FEB8DEECC146B9B1,
        "Gx": 0x188DA80EB03090F67CBF20EB43A18800F4FF0AFD82FF1012,
        "Gy": 0x07192B95FFC8DA78631011ED6B24CDD573F977A11E794811,
        "n":  0xFFFFFFFFFFFFFFFFFFFFFFFF99DEF836146BC9B1B4D22831,
        "desc": "Standard NIST 192 bits"
    }
}


# -------------------------------------------------------------
#  ECDH
# -------------------------------------------------------------

class ECDH:
    def __init__(self, curve, G, n):
        self.curve = curve
        self.G = G
        self.n = n

    def generate_keypair(self):
        priv = random.randint(2, self.n - 1)
        pub  = self.curve.scalar_mult(priv, self.G)
        return priv, pub

    def shared_secret(self, my_priv, their_pub):
        return self.curve.scalar_mult(my_priv, their_pub)


# -------------------------------------------------------------
#  ECDSA
# -------------------------------------------------------------

class ECDSA:
    def __init__(self, curve, G, n):
        self.curve = curve
        self.G = G
        self.n = n

    def generate_keypair(self):
        priv = random.randint(2, self.n - 1)
        pub  = self.curve.scalar_mult(priv, self.G)
        return priv, pub

    def hash_message(self, message):
        h = hashlib.sha256(message.encode()).hexdigest()
        return int(h, 16) % self.n

    def sign(self, message, private_key):
        z = self.hash_message(message)
        r, s = 0, 0
        while r == 0 or s == 0:
            k = random.randint(2, self.n - 1)
            R = self.curve.scalar_mult(k, self.G)
            r = R[0] % self.n
            if r == 0: continue
            k_inv = mod_inverse(k, self.n)
            s = (k_inv * (z + r * private_key)) % self.n
        return (r, s)

    def verify(self, message, signature, public_key):
        r, s = signature
        if not (1 <= r < self.n and 1 <= s < self.n): return False
        z    = self.hash_message(message)
        sinv = mod_inverse(s, self.n)
        u1   = (z * sinv) % self.n
        u2   = (r * sinv) % self.n
        P    = self.curve.point_add(
                   self.curve.scalar_mult(u1, self.G),
                   self.curve.scalar_mult(u2, public_key))
        if P is None: return False
        return P[0] % self.n == r


# -------------------------------------------------------------
#  CHIFFREMENT HYBRIDE ECC + XOR/SHA256
#  METHODE CORRIGEE - fonctionne sur TOUTES les courbes
#  y compris les petites (p=97, p=211)
#  Principe :
#    1. Generer un point secret S = k * Q_destinataire
#    2. Deriver une cle symetrique via SHA256(S)
#    3. Chiffrer le message par XOR avec la cle derivee
#    4. Envoyer (C1=k*G, message_xor)
# -------------------------------------------------------------

class ECCCipher:
    def __init__(self, curve, G, n):
        self.curve = curve
        self.G = G
        self.n = n

    def generate_keypair(self):
        priv = random.randint(2, self.n - 1)
        pub  = self.curve.scalar_mult(priv, self.G)
        return priv, pub

    def _derive_key(self, point):
        """Derive une cle AES-like depuis un point de courbe via SHA256."""
        seed = str(point[0]) + "," + str(point[1])
        return hashlib.sha256(seed.encode()).digest()  # 32 octets

    def encrypt(self, message, pub_key):
        """
        Chiffrement hybride ECC + XOR.
        Retourne (C1, ciphertext_hex, S_affiche).
        Fonctionne sur toutes les courbes independamment de p.
        """
        # Nonce ephemere
        k   = random.randint(2, self.n - 1)
        C1  = self.curve.scalar_mult(k, self.G)       # point public ephemere
        S   = self.curve.scalar_mult(k, pub_key)       # secret partage

        # Derivation de cle
        key = self._derive_key(S)

        # XOR octet par octet (fonctionne pour n importe quel caractere)
        msg_bytes    = message.encode("utf-8")
        cipher_bytes = bytes([msg_bytes[i] ^ key[i % 32]
                               for i in range(len(msg_bytes))])
        return C1, cipher_bytes, S

    def decrypt(self, C1, cipher_bytes, priv_key):
        """Dechiffrement : recalcule S = d * C1 puis XOR inverse."""
        S   = self.curve.scalar_mult(priv_key, C1)
        key = self._derive_key(S)
        plain_bytes = bytes([cipher_bytes[i] ^ key[i % 32]
                              for i in range(len(cipher_bytes))])
        return plain_bytes.decode("utf-8")


# -------------------------------------------------------------
#  COULEURS
# -------------------------------------------------------------

BG      = "#0D0F1A"
BG2     = "#141728"
BG3     = "#1C2035"
BG4     = "#0E1228"
ACCENT  = "#00E5FF"
ACCENT2 = "#7C4DFF"
SUCCESS = "#00E676"
ERROR   = "#FF1744"
WARNING = "#FFD740"
TEXT    = "#E8EAFF"
TEXT2   = "#8892B0"
BORDER  = "#2A3050"
ORANGE  = "#FF6D00"


# -------------------------------------------------------------
#  APPLICATION
# -------------------------------------------------------------

class ECCApp(tk.Tk):

    def __init__(self):
        super().__init__()
        self.title("ECC - Cryptographie a Courbes Elliptiques")
        self.geometry("1280x840")
        self.minsize(1000, 700)
        self.configure(bg=BG)

        self.curve   = None
        self.G       = None
        self.n       = None
        self.ecdh    = None
        self.ecdsa   = None
        self.cipher  = None

        self.alice_priv     = None
        self.alice_pub      = None
        self.bob_priv       = None
        self.bob_pub        = None
        self.sig_priv       = None
        self.sig_pub        = None
        self.signature      = None
        self.chif_priv      = None
        self.chif_pub       = None
        # Stockage chiffrement
        self._enc_C1        = None
        self._ecdsa_enc_C1    = None
        self._ecdsa_enc_bytes = None
        self._ecdsa_bob_priv_val = None
        self._ecdsa_bob_pub_val  = None
        self._enc_bytes     = None

        self._setup_style()
        self._build_header()
        self._build_curve_bar()
        self._build_tabs()
        self._load_curve("Tiny - pedagogique (p=97)")

    # ----------------------------------------------------------
    #  STYLE
    # ----------------------------------------------------------

    def _setup_style(self):
        s = ttk.Style(self)
        s.theme_use("clam")
        s.configure("TNotebook", background=BG, borderwidth=0)
        s.configure("TNotebook.Tab",
                    background=BG3, foreground=TEXT2,
                    padding=[13, 7],
                    font=("Courier New", 9, "bold"))
        s.map("TNotebook.Tab",
              background=[("selected", BG2), ("active", BG3)],
              foreground=[("selected", ACCENT), ("active", TEXT)])
        s.configure("TFrame", background=BG)
        s.configure("TButton",
                    background=ACCENT2, foreground=TEXT,
                    relief="flat", font=("Courier New", 9, "bold"))
        s.map("TButton", background=[("active", "#9B6BFF")])
        s.configure("Green.TButton",
                    background=SUCCESS, foreground="#000",
                    relief="flat", font=("Courier New", 9, "bold"))
        s.map("Green.TButton", background=[("active", "#00C060")])
        s.configure("Red.TButton",
                    background=ERROR, foreground="#fff",
                    relief="flat", font=("Courier New", 9, "bold"))
        s.map("Red.TButton", background=[("active", "#CC0033")])
        s.configure("Orange.TButton",
                    background=ORANGE, foreground="#fff",
                    relief="flat", font=("Courier New", 9, "bold"))
        s.map("Orange.TButton", background=[("active", "#E65100")])
        s.configure("Grey.TButton",
                    background="#37474F", foreground="#fff",
                    relief="flat", font=("Courier New", 9, "bold"))
        s.map("Grey.TButton", background=[("active", "#263238")])

    # ----------------------------------------------------------
    #  HEADER
    # ----------------------------------------------------------

    def _build_header(self):
        hdr = tk.Frame(self, bg=BG)
        hdr.pack(fill="x", padx=16, pady=(8, 2))
        tk.Label(hdr, text="ECC CRYPTOGRAPHY LAB",
                 bg=BG, fg=ACCENT,
                 font=("Courier New", 17, "bold")).pack(side="left")
        tk.Label(hdr, text="   Cryptographie a Courbes Elliptiques",
                 bg=BG, fg=TEXT2,
                 font=("Courier New", 10)).pack(side="left")
        ttk.Button(hdr, text="RESET GLOBAL (tout effacer)",
                   command=self._reset_global,
                   style="Grey.TButton").pack(side="right", padx=4)

    # ----------------------------------------------------------
    #  BARRE COURBE
    # ----------------------------------------------------------

    def _build_curve_bar(self):
        bar = tk.Frame(self, bg=BG2)
        bar.pack(fill="x", padx=10, pady=(0, 4))
        tk.Label(bar, text="  Courbe :",
                 bg=BG2, fg=TEXT2,
                 font=("Courier New", 10)).pack(side="left", padx=(6, 4))
        self.curve_var = tk.StringVar(value="Tiny - pedagogique (p=97)")
        cb = ttk.Combobox(bar, textvariable=self.curve_var,
                          values=list(CURVES.keys()),
                          width=30, state="readonly",
                          font=("Courier New", 9))
        cb.pack(side="left", pady=6, padx=4)
        cb.bind("<<ComboboxSelected>>",
                lambda e: self._load_curve(self.curve_var.get()))
        self.lbl_desc = tk.Label(bar, text="",
                                 bg=BG2, fg=TEXT2,
                                 font=("Courier New", 9))
        self.lbl_desc.pack(side="left", padx=12)
        self.lbl_status = tk.Label(bar, text="COURBE CHARGEE",
                                   bg=BG2, fg=SUCCESS,
                                   font=("Courier New", 9, "bold"))
        self.lbl_status.pack(side="right", padx=12)

    # ----------------------------------------------------------
    #  ONGLETS
    # ----------------------------------------------------------

    def _build_tabs(self):
        self.nb = ttk.Notebook(self)
        self.nb.pack(fill="both", expand=True, padx=10, pady=4)

        self.t_info  = ttk.Frame(self.nb)
        self.t_ecdh  = ttk.Frame(self.nb)
        self.t_chif  = ttk.Frame(self.nb)
        self.t_ecdsa = ttk.Frame(self.nb)
        self.t_ops   = ttk.Frame(self.nb)
        self.t_about  = ttk.Frame(self.nb)
        self.t_comms = ttk.Frame(self.nb)

        self.nb.add(self.t_info,  text="  1 - Courbe & Visualisation  ")
        self.nb.add(self.t_ecdh,  text="  2 - ECDH Echange Cles  ")
        self.nb.add(self.t_chif,  text="  3 - Chiffrement / Dechiffrement  ")
        self.nb.add(self.t_ecdsa, text="  4 - ECDSA Signature  ")
        self.nb.add(self.t_ops,   text="  5 - Operations Manuelles  ")
        self.nb.add(self.t_about, text="  6 - Theorie  ")
        self.nb.add(self.t_comms, text="  7 - Communication Complete  ")

        self._tab_info()
        self._tab_ecdh()
        self._tab_chiffrement()
        self._tab_ecdsa()
        self._tab_ops()
        self._tab_about()
        self._tab_communication()

    # ----------------------------------------------------------
    #  UTILITAIRE : barre effacer
    # ----------------------------------------------------------

    def _barre_effacer(self, parent, bg, actions):
        barre = tk.Frame(parent, bg=bg, pady=3)
        barre.pack(fill="x", padx=6, pady=(2, 4))
        tk.Label(barre, text="  Nettoyage : ",
                 bg=bg, fg=TEXT2,
                 font=("Courier New", 8, "bold")).pack(side="left", padx=(2, 6))
        for label, cmd in actions:
            ttk.Button(barre, text=label,
                       command=cmd,
                       style="Orange.TButton").pack(side="left", padx=2)
        return barre

    def _clear_entry(self, entry, placeholder=""):
        entry.delete(0, "end")
        if placeholder:
            entry.insert(0, placeholder)

    def _clear_text(self, widget):
        try:
            widget.configure(state="normal")
        except Exception:
            pass
        widget.delete("1.0", "end")
        try:
            widget.configure(state="disabled")
        except Exception:
            pass

    # ----------------------------------------------------------
    #  ONGLET 1 : VISUALISATION
    # ----------------------------------------------------------

    def _tab_info(self):
        parent = self.t_info

        left = tk.Frame(parent, bg=BG2)
        left.pack(side="left", fill="both", expand=True, padx=8, pady=8)

        titre_f = tk.Frame(left, bg=BG4)
        titre_f.pack(fill="x", padx=2, pady=(4, 0))
        tk.Label(titre_f,
                 text="  VISUALISATION DE LA COURBE ELLIPTIQUE",
                 bg=BG4, fg=ACCENT,
                 font=("Courier New", 11, "bold")).pack(side="left", pady=5)
        tk.Label(titre_f, text="Corps fini Fp  ",
                 bg=BG4, fg=TEXT2,
                 font=("Courier New", 9)).pack(side="right", pady=5)

        self.lbl_eq_active = tk.Label(left,
                 text="y^2 = x^3 + 2x + 3  (mod 97)",
                 bg=BG2, fg=ACCENT2,
                 font=("Courier New", 9, "bold"))
        self.lbl_eq_active.pack(pady=(4, 2))

        self.canvas = tk.Canvas(left, bg="#07091A",
                                width=570, height=380,
                                highlightthickness=2,
                                highlightbackground=ACCENT2)
        self.canvas.pack(padx=6, pady=4)

        btn_row = tk.Frame(left, bg=BG2)
        btn_row.pack(pady=4, fill="x", padx=6)
        ttk.Button(btn_row, text="Rafraichir graphique",
                   command=self._draw_curve).pack(side="left", padx=4)
        ttk.Button(btn_row, text="Animer k*G",
                   command=self._animate_mult,
                   style="Green.TButton").pack(side="left", padx=4)
        ttk.Button(btn_row, text="Effacer animation",
                   command=self._draw_curve,
                   style="Orange.TButton").pack(side="left", padx=4)

        leg = tk.Frame(left, bg="#0A0C1E")
        leg.pack(fill="x", padx=6, pady=(0, 2))
        tk.Label(leg, text="  Legende : ",
                 bg="#0A0C1E", fg=TEXT2,
                 font=("Courier New", 8)).pack(side="left", pady=3)
        tk.Label(leg, text="● Point G",
                 bg="#0A0C1E", fg=ACCENT,
                 font=("Courier New", 8)).pack(side="left", padx=10)
        tk.Label(leg, text="● Points courbe",
                 bg="#0A0C1E", fg="#4FC3F7",
                 font=("Courier New", 8)).pack(side="left", padx=10)
        tk.Label(leg, text="● k*G animes",
                 bg="#0A0C1E", fg=SUCCESS,
                 font=("Courier New", 8)).pack(side="left", padx=10)

        right = tk.Frame(parent, bg=BG2, width=310)
        right.pack(side="right", fill="both", padx=(0, 8), pady=8)
        right.pack_propagate(False)

        tk.Label(right, text="Parametres de la Courbe",
                 bg=BG2, fg=ACCENT,
                 font=("Courier New", 11, "bold")).pack(pady=(10, 4))

        rapide_f = tk.Frame(right, bg=BG3)
        rapide_f.pack(fill="x", padx=6, pady=(0, 4))
        tk.Label(rapide_f, text="Changer de courbe :",
                 bg=BG3, fg=TEXT2,
                 font=("Courier New", 8)).pack(anchor="w", padx=6, pady=(4, 2))
        r1 = tk.Frame(rapide_f, bg=BG3)
        r1.pack(fill="x", padx=4, pady=(0, 6))
        for nom, label in [
            ("Tiny - pedagogique (p=97)",    "p=97"),
            ("Petite - pedagogique (p=211)", "p=211"),
            ("secp256k1 - Bitcoin",          "Bitcoin"),
            ("secp192r1 - NIST P-192",       "NIST")
        ]:
            ttk.Button(r1, text=label,
                       command=lambda n=nom: self._charger_rapide(n)
                       ).pack(side="left", padx=2)

        self.txt_info = scrolledtext.ScrolledText(
            right, bg=BG3, fg=TEXT,
            font=("Courier New", 9),
            relief="flat", wrap="word",
            width=33, height=22)
        self.txt_info.pack(padx=6, pady=4, fill="both", expand=True)
        self._add_tags(self.txt_info)

        self._barre_effacer(right, BG2, [
            ("Effacer les infos",
             lambda: self._clear_text(self.txt_info)),
            ("Effacer le graphique",
             lambda: self.canvas.delete("all")),
        ])

    # ----------------------------------------------------------
    #  ONGLET 2 : ECDH
    # ----------------------------------------------------------

    def _tab_ecdh(self):
        parent = self.t_ecdh

        tk.Label(parent, text="ECHANGE DE CLES DIFFIE-HELLMAN (ECDH)",
                 bg=BG, fg=ACCENT,
                 font=("Courier New", 12, "bold")).pack(
                 anchor="w", padx=14, pady=(10, 4))

        row = tk.Frame(parent, bg=BG)
        row.pack(fill="both", expand=True, padx=8)

        frm_a = tk.LabelFrame(row, text=" ALICE ",
                              bg=BG2, fg=ACCENT2,
                              font=("Courier New", 11, "bold"),
                              relief="solid", bd=1)
        frm_a.pack(side="left", fill="both", expand=True,
                   padx=(0, 4), pady=6)
        frm_b = tk.LabelFrame(row, text=" BOB ",
                              bg=BG2, fg=WARNING,
                              font=("Courier New", 11, "bold"),
                              relief="solid", bd=1)
        frm_b.pack(side="right", fill="both", expand=True,
                   padx=(4, 0), pady=6)

        self._ecdh_panel(frm_a, "alice", ACCENT2)
        self._ecdh_panel(frm_b, "bob",   WARNING)

        frm_s = tk.Frame(parent, bg=BG3)
        frm_s.pack(fill="x", padx=8, pady=(0, 2))

        tk.Label(frm_s, text="SECRET PARTAGE",
                 bg=BG3, fg=ACCENT,
                 font=("Courier New", 10, "bold")).pack(pady=(6, 2))

        self.txt_ecdh = scrolledtext.ScrolledText(
            frm_s, bg="#04060F", fg=SUCCESS,
            font=("Courier New", 9),
            height=5, relief="flat", wrap="word")
        self.txt_ecdh.pack(fill="x", padx=8, pady=(0, 4))
        self._add_tags(self.txt_ecdh)

        btn_ecdh = tk.Frame(frm_s, bg=BG3)
        btn_ecdh.pack(pady=(0, 4))
        ttk.Button(btn_ecdh, text="CALCULER LE SECRET PARTAGE",
                   command=self._calc_ecdh_secret,
                   style="Green.TButton").pack(side="left", padx=6)

        self._barre_effacer(frm_s, BG3, [
            ("Effacer cles Alice",  self._reset_alice),
            ("Effacer cles Bob",    self._reset_bob),
            ("Effacer le secret",
             lambda: self._clear_text(self.txt_ecdh)),
            ("Tout effacer",        self._reset_ecdh_complet),
        ])

    def _ecdh_panel(self, parent, who, color):
        tk.Label(parent, text="Cle privee :",
                 bg=BG2, fg=TEXT2,
                 font=("Courier New", 9)).pack(anchor="w", padx=10, pady=(10, 2))
        ent_priv = tk.Entry(parent, bg=BG3, fg=color,
                            font=("Courier New", 9),
                            insertbackground=ACCENT, relief="flat", bd=3)
        ent_priv.pack(fill="x", padx=10)
        ent_priv.insert(0, "(cliquer Generer)")

        tk.Label(parent, text="Cle publique :",
                 bg=BG2, fg=TEXT2,
                 font=("Courier New", 9)).pack(anchor="w", padx=10, pady=(8, 2))
        txt_pub = tk.Text(parent, bg=BG3, fg=color,
                          font=("Courier New", 8),
                          relief="flat", bd=3, height=3, wrap="word")
        txt_pub.pack(fill="x", padx=10)

        tk.Label(parent,
                 text="  Entrer d manuellement ou cliquer Generer",
                 bg=BG2, fg=TEXT2,
                 font=("Courier New", 8, "italic")).pack(anchor="w", padx=10)

        btn_row = tk.Frame(parent, bg=BG2)
        btn_row.pack(pady=8)
        ttk.Button(btn_row,
                   text="Generer cles " + who.title(),
                   command=lambda: self._gen_ecdh(who, ent_priv, txt_pub)
                   ).pack(side="left", padx=4)
        ttk.Button(btn_row,
                   text="Calculer Q depuis d",
                   command=lambda: self._calc_pub_from_priv_ecdh(who, ent_priv, txt_pub)
                   ).pack(side="left", padx=4)
        ttk.Button(btn_row, text="Effacer",
                   command=lambda: self._reset_ecdh_user(who, ent_priv, txt_pub),
                   style="Orange.TButton").pack(side="left", padx=4)

        if who == "alice":
            self.ent_alice_priv = ent_priv
            self.txt_alice_pub  = txt_pub
        else:
            self.ent_bob_priv = ent_priv
            self.txt_bob_pub  = txt_pub

    # ----------------------------------------------------------
    #  ONGLET 3 : CHIFFREMENT / DECHIFFREMENT  (CORRIGE)
    # ----------------------------------------------------------

    def _tab_chiffrement(self):
        parent = self.t_chif

        # ── En-tete + Cles (ligne unique) ────────────────────────
        hdr = tk.Frame(parent, bg=BG4)
        hdr.pack(fill="x", padx=6, pady=(4, 2))
        tk.Label(hdr, text="  CHIFFREMENT / DECHIFFREMENT ECC",
                 bg=BG4, fg=ACCENT,
                 font=("Courier New", 10, "bold")).pack(side="left", pady=3)
        self.lbl_chif_etat = tk.Label(hdr,
            text="  |  En attente des cles...",
            bg=BG4, fg=TEXT2, font=("Courier New", 8))
        self.lbl_chif_etat.pack(side="left", pady=3)
        ttk.Button(hdr, text="TEST AUTO",
                   command=self._test_auto_chiffrement,
                   style="Grey.TButton").pack(side="right", padx=6, pady=3)

        # ── Cles sur une seule ligne compacte ─────────────────────
        frm_k = tk.LabelFrame(parent, text="  Cles  ",
                              bg=BG2, fg=WARNING,
                              font=("Courier New", 9, "bold"),
                              relief="solid", bd=1)
        frm_k.pack(fill="x", padx=6, pady=(2, 2))
        rk = tk.Frame(frm_k, bg=BG2)
        rk.pack(fill="x", padx=8, pady=4)
        rk.columnconfigure(1, weight=1)
        rk.columnconfigure(3, weight=1)

        tk.Label(rk, text="d prive :", bg=BG2, fg=TEXT2,
                 font=("Courier New", 9), anchor="w").grid(
                 row=0, column=0, sticky="w", padx=(0, 4))
        self.ent_chif_priv = tk.Entry(rk, bg=BG3, fg=ACCENT2,
                                      font=("Courier New", 9),
                                      insertbackground=ACCENT,
                                      relief="flat", bd=3)
        self.ent_chif_priv.grid(row=0, column=1, padx=4, sticky="ew")
        self.ent_chif_priv.insert(0, "(saisir ou Generer)")

        tk.Label(rk, text="  Q public :", bg=BG2, fg=TEXT2,
                 font=("Courier New", 9), anchor="w").grid(
                 row=0, column=2, sticky="w", padx=(8, 4))
        self.ent_chif_pub = tk.Entry(rk, bg=BG3, fg=SUCCESS,
                                     font=("Courier New", 9),
                                     insertbackground=ACCENT,
                                     relief="flat", bd=3)
        self.ent_chif_pub.grid(row=0, column=3, padx=4, sticky="ew")
        self.ent_chif_pub.insert(0, "(calculee auto)")

        bk = tk.Frame(frm_k, bg=BG2)
        bk.pack(pady=(0, 4))
        ttk.Button(bk, text="Generer",
                   command=self._gen_chif_keys).pack(side="left", padx=3)
        ttk.Button(bk, text="Calculer Q depuis d",
                   command=self._calc_chif_pub_from_priv,
                   style="Green.TButton").pack(side="left", padx=3)
        ttk.Button(bk, text="Effacer",
                   command=self._reset_chif_keys,
                   style="Orange.TButton").pack(side="left", padx=3)

        # ── Deux colonnes : Chiffrement | Dechiffrement ───────────
        cols = tk.Frame(parent, bg=BG)
        cols.pack(fill="both", expand=True, padx=6, pady=2)
        cols.columnconfigure(0, weight=1)
        cols.columnconfigure(1, weight=1)

        # GAUCHE : Chiffrement
        col_enc = tk.LabelFrame(cols,
                                text="  CHIFFREMENT  ",
                                bg=BG2, fg=ACCENT2,
                                font=("Courier New", 9, "bold"),
                                relief="solid", bd=1)
        col_enc.grid(row=0, column=0, sticky="nsew", padx=(0, 3), pady=2)

        tk.Label(col_enc, text="Message en clair :",
                 bg=BG2, fg=TEXT2,
                 font=("Courier New", 9)).pack(anchor="w", padx=8, pady=(8, 2))
        msg_row = tk.Frame(col_enc, bg=BG2)
        msg_row.pack(fill="x", padx=8, pady=(0, 4))
        self.ent_plain = tk.Entry(msg_row, bg=BG3, fg=TEXT,
                                  font=("Courier New", 10),
                                  insertbackground=ACCENT,
                                  relief="flat", bd=3)
        self.ent_plain.pack(side="left", fill="x", expand=True)
        self.ent_plain.insert(0, "Bonjour ECC !")
        ttk.Button(msg_row, text="X",
                   command=lambda: self._clear_entry(self.ent_plain, ""),
                   style="Orange.TButton").pack(side="left", padx=4)

        ttk.Button(col_enc, text="CHIFFRER LE MESSAGE",
                   command=self._chiffrer,
                   style="Green.TButton").pack(pady=4)

        tk.Label(col_enc, text="Resultat chiffre (illisible) :",
                 bg=BG2, fg=WARNING,
                 font=("Courier New", 9)).pack(anchor="w", padx=8, pady=(4, 2))
        self.txt_cipher = scrolledtext.ScrolledText(
            col_enc, bg="#04060F", fg=WARNING,
            font=("Courier New", 9),
            height=6, relief="flat", wrap="word")
        self.txt_cipher.pack(fill="both", expand=True, padx=8, pady=(0, 8))
        self._add_tags(self.txt_cipher)

        # DROITE : Dechiffrement
        col_dec = tk.LabelFrame(cols,
                                text="  DECHIFFREMENT  ",
                                bg=BG2, fg=SUCCESS,
                                font=("Courier New", 9, "bold"),
                                relief="solid", bd=1)
        col_dec.grid(row=0, column=1, sticky="nsew", padx=(3, 0), pady=2)

        tk.Label(col_dec,
                 text="Utilise la meme cle privee d pour retrouver le message :",
                 bg=BG2, fg=TEXT2,
                 font=("Courier New", 8, "italic"),
                 wraplength=220, justify="left").pack(
                 anchor="w", padx=8, pady=(8, 4))

        ttk.Button(col_dec, text="DECHIFFRER LE MESSAGE",
                   command=self._dechiffrer,
                   style="Red.TButton").pack(pady=4)

        tk.Label(col_dec, text="Message dechiffre :",
                 bg=BG2, fg=SUCCESS,
                 font=("Courier New", 9)).pack(anchor="w", padx=8, pady=(4, 2))
        self.txt_decrypted = scrolledtext.ScrolledText(
            col_dec, bg="#030F03", fg=SUCCESS,
            font=("Courier New", 12, "bold"),
            height=6, relief="flat", wrap="word")
        self.txt_decrypted.pack(fill="both", expand=True, padx=8, pady=(0, 4))
        self._add_tags(self.txt_decrypted)

        ttk.Button(col_dec, text="Effacer tout",
                   command=self._reset_chiffrement_complet,
                   style="Orange.TButton").pack(pady=(0, 8))

    # ----------------------------------------------------------
    #  ONGLET 4 : ECDSA
    # ----------------------------------------------------------

    def _tab_ecdsa(self):
        parent = self.t_ecdsa

        # En-tete
        hdr = tk.Frame(parent, bg=BG4)
        hdr.pack(fill="x", padx=6, pady=(4, 2))
        tk.Label(hdr, text="  SIGNATURE NUMERIQUE ECDSA",
                 bg=BG4, fg=ACCENT,
                 font=("Courier New", 10, "bold")).pack(side="left", pady=3)
        ttk.Button(hdr, text="Effacer tout",
                   command=self._reset_ecdsa_complet,
                   style="Orange.TButton").pack(side="right", padx=6, pady=3)

        # Cles sur une ligne compacte
        frm_k = tk.LabelFrame(parent, text="  Cles du signataire (Alice)  ",
                              bg=BG2, fg=ACCENT2,
                              font=("Courier New", 9, "bold"),
                              relief="solid", bd=1)
        frm_k.pack(fill="x", padx=6, pady=2)
        rk = tk.Frame(frm_k, bg=BG2)
        rk.pack(fill="x", padx=8, pady=4)
        rk.columnconfigure(1, weight=1)
        rk.columnconfigure(3, weight=1)
        tk.Label(rk, text="d prive Alice :", bg=BG2, fg=TEXT2,
                 font=("Courier New", 9), anchor="w").grid(
                 row=0, column=0, sticky="w", padx=(0, 4))
        self.ent_sig_priv = tk.Entry(rk, bg=BG3, fg=ACCENT2,
                                     font=("Courier New", 9),
                                     insertbackground=ACCENT,
                                     relief="flat", bd=3)
        self.ent_sig_priv.grid(row=0, column=1, padx=4, sticky="ew")
        self.ent_sig_priv.insert(0, "(saisir d ou Generer)")
        tk.Label(rk, text="  Q public Alice :", bg=BG2, fg=TEXT2,
                 font=("Courier New", 9), anchor="w").grid(
                 row=0, column=2, sticky="w", padx=(8, 4))
        self.ent_sig_pub = tk.Entry(rk, bg=BG3, fg=SUCCESS,
                                    font=("Courier New", 9),
                                    insertbackground=ACCENT,
                                    relief="flat", bd=3)
        self.ent_sig_pub.grid(row=0, column=3, padx=4, sticky="ew")
        self.ent_sig_pub.insert(0, "(calculee auto)")
        bk = tk.Frame(frm_k, bg=BG2)
        bk.pack(pady=(0, 4))
        ttk.Button(bk, text="Generer",
                   command=self._gen_ecdsa_keys).pack(side="left", padx=3)
        ttk.Button(bk, text="Calculer Q depuis d",
                   command=self._calc_ecdsa_pub_from_priv,
                   style="Green.TButton").pack(side="left", padx=3)
        ttk.Button(bk, text="Effacer cles",
                   command=self._reset_ecdsa_keys,
                   style="Orange.TButton").pack(side="left", padx=3)

        # Cle publique de Bob (pour chiffrer le message)
        frm_bob = tk.LabelFrame(parent, text="  Cle publique de Bob (destinataire)  ",
                                bg=BG2, fg="#B39DDB",
                                font=("Courier New", 9, "bold"),
                                relief="solid", bd=1)
        frm_bob.pack(fill="x", padx=6, pady=2)
        rb = tk.Frame(frm_bob, bg=BG2)
        rb.pack(fill="x", padx=8, pady=4)
        rb.columnconfigure(1, weight=1)
        rb.columnconfigure(3, weight=1)
        tk.Label(rb, text="d prive Bob :", bg=BG2, fg=TEXT2,
                 font=("Courier New", 9), anchor="w").grid(
                 row=0, column=0, sticky="w", padx=(0, 4))
        self._ecdsa_bob_priv_ent = tk.Entry(rb, bg=BG3, fg=ACCENT2,
                                     font=("Courier New", 9),
                                     insertbackground=ACCENT,
                                     relief="flat", bd=3)
        self._ecdsa_bob_priv_ent.grid(row=0, column=1, padx=4, sticky="ew")
        self._ecdsa_bob_priv_ent.insert(0, "(saisir d ou Generer)")
        tk.Label(rb, text="  Q public Bob :", bg=BG2, fg=TEXT2,
                 font=("Courier New", 9), anchor="w").grid(
                 row=0, column=2, sticky="w", padx=(8, 4))
        self._ecdsa_bob_pub_ent = tk.Entry(rb, bg=BG3, fg="#B39DDB",
                                    font=("Courier New", 9),
                                    insertbackground=ACCENT,
                                    relief="flat", bd=3)
        self._ecdsa_bob_pub_ent.grid(row=0, column=3, padx=4, sticky="ew")
        self._ecdsa_bob_pub_ent.insert(0, "(calculee auto)")
        self._ecdsa_bob_priv_val = None
        self._ecdsa_bob_pub_val  = None
        bkb = tk.Frame(frm_bob, bg=BG2)
        bkb.pack(pady=(0, 4))
        ttk.Button(bkb, text="Generer cles Bob",
                   command=self._ecdsa_gen_bob).pack(side="left", padx=3)
        ttk.Button(bkb, text="Calculer Q Bob depuis d",
                   command=self._ecdsa_calc_bob,
                   style="Green.TButton").pack(side="left", padx=3)

        # 3 colonnes : Alice | Reseau | Bob
        cols = tk.Frame(parent, bg=BG)
        cols.pack(fill="both", expand=True, padx=6, pady=2)
        cols.columnconfigure(0, weight=3)
        cols.columnconfigure(1, weight=4)
        cols.columnconfigure(2, weight=3)

        # --- ALICE (signataire + chiffre) ---
        col_alice = tk.LabelFrame(cols,
                                  text="  ALICE  (Signataire)  ",
                                  bg=BG2, fg="#00E5FF",
                                  font=("Courier New", 9, "bold"),
                                  relief="solid", bd=2)
        col_alice.grid(row=0, column=0, sticky="nsew", padx=(0, 3), pady=2)

        tk.Label(col_alice, text="Message en clair :",
                 bg=BG2, fg=TEXT2,
                 font=("Courier New", 9)).pack(anchor="w", padx=8, pady=(8, 2))
        self.ent_message = tk.Entry(col_alice, bg=BG3, fg=TEXT,
                                    font=("Courier New", 10),
                                    insertbackground=ACCENT,
                                    relief="flat", bd=3)
        self.ent_message.pack(fill="x", padx=8)
        self.ent_message.insert(0, "Bonjour Bob !")

        ttk.Button(col_alice,
                   text="CHIFFRER + SIGNER",
                   command=self._signer,
                   style="Green.TButton").pack(pady=6)

        tk.Label(col_alice, text="Signature (r, s) produite :",
                 bg=BG2, fg=TEXT2,
                 font=("Courier New", 8)).pack(anchor="w", padx=8, pady=(4, 1))
        self._sig_lbl_r = tk.Label(col_alice, text="r = ---",
                 bg=BG3, fg=SUCCESS,
                 font=("Courier New", 8),
                 anchor="w", wraplength=180, justify="left")
        self._sig_lbl_r.pack(fill="x", padx=8, pady=(0, 1))
        self._sig_lbl_s = tk.Label(col_alice, text="s = ---",
                 bg=BG3, fg=SUCCESS,
                 font=("Courier New", 8),
                 anchor="w", wraplength=180, justify="left")
        self._sig_lbl_s.pack(fill="x", padx=8, pady=(0, 4))
        tk.Label(col_alice,
                 text="  Seul Alice peut produire\n  cette signature",
                 bg=BG2, fg=TEXT2,
                 font=("Courier New", 7, "italic"),
                 justify="left").pack(anchor="w", padx=8, pady=(0, 8))

        # --- RESEAU PUBLIC ---
        col_net = tk.LabelFrame(cols,
                                text="  RESEAU PUBLIC  --  Tout le monde voit ceci  ",
                                bg="#08080F", fg=WARNING,
                                font=("Courier New", 9, "bold"),
                                relief="solid", bd=2)
        col_net.grid(row=0, column=1, sticky="nsew", padx=3, pady=2)

        tk.Label(col_net,
                 text="Q publique d'Alice (connue de tous) :",
                 bg="#08080F", fg=TEXT2,
                 font=("Courier New", 8)).pack(anchor="w", padx=8, pady=(6, 0))
        self._ecdsa_net_qalice = tk.Label(col_net,
                 text="(en attente...)",
                 bg="#08080F", fg=SUCCESS,
                 font=("Courier New", 8),
                 wraplength=250, justify="left")
        self._ecdsa_net_qalice.pack(anchor="w", padx=8, pady=(0, 6))

        net_m = tk.LabelFrame(col_net,
                              text="  Message chiffre en transit  --  ILLISIBLE  ",
                              bg="#0A0A0F", fg=WARNING,
                              font=("Courier New", 8, "bold"),
                              relief="solid", bd=1)
        net_m.pack(fill="both", expand=True, padx=6, pady=(0, 4))

        tk.Label(net_m, text="Point ephemere C1 :",
                 bg="#0A0A0F", fg=TEXT2,
                 font=("Courier New", 8)).pack(anchor="w", padx=8, pady=(6, 0))
        self._ecdsa_net_c1 = tk.Label(net_m,
                 text="(en attente...)",
                 bg="#0A0A0F", fg=ACCENT,
                 font=("Courier New", 8),
                 wraplength=250, justify="left")
        self._ecdsa_net_c1.pack(anchor="w", padx=8, pady=(0, 4))

        tk.Label(net_m, text="Octets chiffres (hex) :",
                 bg="#0A0A0F", fg=TEXT2,
                 font=("Courier New", 8)).pack(anchor="w", padx=8)
        self._ecdsa_net_hex = scrolledtext.ScrolledText(net_m,
                 bg="#020208", fg=WARNING,
                 font=("Courier New", 8),
                 height=3, relief="flat", wrap="word",
                 state="disabled")
        self._ecdsa_net_hex.pack(fill="x", padx=8, pady=(2, 4))

        tk.Label(net_m, text="Signature (r, s) :",
                 bg="#0A0A0F", fg=TEXT2,
                 font=("Courier New", 8)).pack(anchor="w", padx=8)
        self._ecdsa_net_sig = tk.Label(net_m,
                 text="(en attente...)",
                 bg="#0A0A0F", fg=SUCCESS,
                 font=("Courier New", 8),
                 wraplength=250, justify="left")
        self._ecdsa_net_sig.pack(anchor="w", padx=8, pady=(0, 4))

        intru = tk.Frame(col_net, bg="#150505")
        intru.pack(fill="x", padx=6, pady=(0, 6))
        tk.Label(intru,
                 text="Personne A : lit les octets chiffres...  ECHEC (illisible)\n"
                      "Personne B : modifie le message...       ECHEC (signature invalide)\n"
                      "Seul Bob (cle privee) peut dechiffrer !",
                 bg="#150505", fg=ERROR,
                 font=("Courier New", 8), justify="left").pack(
                 anchor="w", padx=8, pady=6)

        # --- BOB (destinataire + verificateur) ---
        col_bob = tk.LabelFrame(cols,
                                text="  BOB  (Destinataire)  ",
                                bg=BG2, fg="#B39DDB",
                                font=("Courier New", 9, "bold"),
                                relief="solid", bd=2)
        col_bob.grid(row=0, column=2, sticky="nsew", padx=(3, 0), pady=2)

        tk.Label(col_bob,
                 text="Bob utilise sa cle\nprivee pour dechiffrer\net verifier l'identite\nd'Alice :",
                 bg=BG2, fg=TEXT2,
                 font=("Courier New", 8, "italic"),
                 justify="left").pack(anchor="w", padx=8, pady=(8, 4))

        ttk.Button(col_bob,
                   text="DECHIFFRER + VERIFIER",
                   command=self._verifier,
                   style="Green.TButton").pack(padx=8, pady=4)

        tk.Label(col_bob, text="Resultat :",
                 bg=BG2, fg=TEXT2,
                 font=("Courier New", 9)).pack(anchor="w", padx=8, pady=(4, 2))
        self.txt_ecdsa = scrolledtext.ScrolledText(
            col_bob, bg="#04060F", fg=TEXT,
            font=("Courier New", 9), relief="flat", wrap="word")
        self.txt_ecdsa.pack(fill="both", expand=True, padx=8, pady=(0, 8))
        self._add_tags(self.txt_ecdsa)

        # Variables internes
        self._ecdsa_enc_C1    = None
        self._ecdsa_enc_bytes = None


    #  ONGLET 5 : OPERATIONS MANUELLES (redesign complet)
    # ----------------------------------------------------------

    def _tab_ops(self):
        parent = self.t_ops

        # Titre
        tk.Label(parent, text="OPERATIONS MANUELLES SUR LA COURBE",
                 bg=BG, fg=ACCENT,
                 font=("Courier New", 12, "bold")).pack(
                 anchor="w", padx=14, pady=(10, 2))
        tk.Label(parent,
                 text="Calculez vous-meme l addition et la multiplication de points",
                 bg=BG, fg=TEXT2,
                 font=("Courier New", 9)).pack(anchor="w", padx=14, pady=(0, 6))

        # Conteneur deux colonnes
        cols = tk.Frame(parent, bg=BG)
        cols.pack(fill="both", expand=True, padx=8, pady=4)

        # ── COLONNE GAUCHE : Addition ──
        col_left = tk.Frame(cols, bg=BG)
        col_left.pack(side="left", fill="both", expand=True, padx=(0, 4))

        frm_add = tk.LabelFrame(col_left,
                                text="  ADDITION DE POINTS  P + Q  ",
                                bg=BG2, fg=ACCENT2,
                                font=("Courier New", 10, "bold"),
                                relief="solid", bd=1)
        frm_add.pack(fill="both", expand=True, pady=4)

        # Explication
        tk.Label(frm_add,
                 text="Additionner deux points P et Q sur la courbe.",
                 bg=BG2, fg=TEXT2,
                 font=("Courier New", 8, "italic")).pack(
                 anchor="w", padx=10, pady=(6, 0))
        tk.Label(frm_add,
                 text="Entrez les coordonnees x et y de chaque point.",
                 bg=BG2, fg=TEXT2,
                 font=("Courier New", 8, "italic")).pack(
                 anchor="w", padx=10, pady=(0, 8))

        # Point P
        frm_P = tk.LabelFrame(frm_add, text=" Point P ",
                              bg=BG3, fg=ACCENT,
                              font=("Courier New", 9, "bold"),
                              relief="flat", bd=1)
        frm_P.pack(fill="x", padx=10, pady=4)
        r_P = tk.Frame(frm_P, bg=BG3)
        r_P.pack(pady=8)
        tk.Label(r_P, text="x de P :", bg=BG3, fg=TEXT2,
                 font=("Courier New", 9)).pack(side="left", padx=(10, 4))
        self.e_px = tk.Entry(r_P, bg=BG, fg=ACCENT,
                             font=("Courier New", 10, "bold"),
                             width=8, relief="flat", bd=3,
                             justify="center")
        self.e_px.pack(side="left", padx=2)
        self.e_px.insert(0, "3")
        tk.Label(r_P, text="y de P :", bg=BG3, fg=TEXT2,
                 font=("Courier New", 9)).pack(side="left", padx=(16, 4))
        self.e_py = tk.Entry(r_P, bg=BG, fg=ACCENT,
                             font=("Courier New", 10, "bold"),
                             width=8, relief="flat", bd=3,
                             justify="center")
        self.e_py.pack(side="left", padx=2)
        self.e_py.insert(0, "6")

        # Symbole +
        tk.Label(frm_add, text="+", bg=BG2, fg=WARNING,
                 font=("Courier New", 18, "bold")).pack()

        # Point Q
        frm_Q = tk.LabelFrame(frm_add, text=" Point Q ",
                              bg=BG3, fg=ACCENT2,
                              font=("Courier New", 9, "bold"),
                              relief="flat", bd=1)
        frm_Q.pack(fill="x", padx=10, pady=4)
        r_Q = tk.Frame(frm_Q, bg=BG3)
        r_Q.pack(pady=8)
        tk.Label(r_Q, text="x de Q :", bg=BG3, fg=TEXT2,
                 font=("Courier New", 9)).pack(side="left", padx=(10, 4))
        self.e_qx = tk.Entry(r_Q, bg=BG, fg=ACCENT2,
                             font=("Courier New", 10, "bold"),
                             width=8, relief="flat", bd=3,
                             justify="center")
        self.e_qx.pack(side="left", padx=2)
        self.e_qx.insert(0, "39")  # Autre point valide sur p=97
        tk.Label(r_Q, text="y de Q :", bg=BG3, fg=TEXT2,
                 font=("Courier New", 9)).pack(side="left", padx=(16, 4))
        self.e_qy = tk.Entry(r_Q, bg=BG, fg=ACCENT2,
                             font=("Courier New", 10, "bold"),
                             width=8, relief="flat", bd=3,
                             justify="center")
        self.e_qy.pack(side="left", padx=2)
        self.e_qy.insert(0, "91")  # (39,91) est sur la courbe p=97

        # Boutons
        btn_add = tk.Frame(frm_add, bg=BG2)
        btn_add.pack(pady=8)
        ttk.Button(btn_add, text="Calculer P + Q",
                   command=self._do_add,
                   style="Green.TButton").pack(side="left", padx=4)
        ttk.Button(btn_add, text="Remettre a zero",
                   command=self._reset_add_fields,
                   style="Orange.TButton").pack(side="left", padx=4)
        ttk.Button(btn_add, text="Utiliser G comme P",
                   command=self._use_G_as_P).pack(side="left", padx=4)
        ttk.Button(btn_add, text="Voir points valides",
                   command=self._show_valid_points).pack(side="left", padx=4)

        # Resultat addition
        res_add_f = tk.LabelFrame(frm_add, text=" Resultat  P + Q = ? ",
                                  bg=BG3, fg=SUCCESS,
                                  font=("Courier New", 9, "bold"),
                                  relief="flat", bd=1)
        res_add_f.pack(fill="x", padx=10, pady=(4, 10))
        self.lbl_add_result = tk.Label(res_add_f,
                                       text="(cliquer Calculer)",
                                       bg=BG3, fg=TEXT2,
                                       font=("Courier New", 11, "bold"),
                                       wraplength=260)
        self.lbl_add_result.pack(pady=10, padx=10)

        # ── COLONNE DROITE : Multiplication ──
        col_right = tk.Frame(cols, bg=BG)
        col_right.pack(side="right", fill="both", expand=True, padx=(4, 0))

        frm_mul = tk.LabelFrame(col_right,
                                text="  MULTIPLICATION SCALAIRE  k * P  ",
                                bg=BG2, fg=WARNING,
                                font=("Courier New", 10, "bold"),
                                relief="solid", bd=1)
        frm_mul.pack(fill="both", expand=True, pady=4)

        # Explication
        tk.Label(frm_mul,
                 text="Multiplier un point P par un entier k.",
                 bg=BG2, fg=TEXT2,
                 font=("Courier New", 8, "italic")).pack(
                 anchor="w", padx=10, pady=(6, 0))
        tk.Label(frm_mul,
                 text="k = nombre de fois qu on additionne P avec lui-meme.",
                 bg=BG2, fg=TEXT2,
                 font=("Courier New", 8, "italic")).pack(
                 anchor="w", padx=10, pady=(0, 8))

        # Scalaire k
        frm_k_val = tk.LabelFrame(frm_mul, text=" Scalaire k ",
                                  bg=BG3, fg=WARNING,
                                  font=("Courier New", 9, "bold"),
                                  relief="flat", bd=1)
        frm_k_val.pack(fill="x", padx=10, pady=4)
        r_k = tk.Frame(frm_k_val, bg=BG3)
        r_k.pack(pady=8)
        tk.Label(r_k,
                 text="k = (entier, ex: 2 = P+P, 3 = P+P+P) :",
                 bg=BG3, fg=TEXT2,
                 font=("Courier New", 9)).pack(side="left", padx=(10, 8))
        self.e_k = tk.Entry(r_k, bg=BG, fg=WARNING,
                            font=("Courier New", 14, "bold"),
                            width=6, relief="flat", bd=3,
                            justify="center")
        self.e_k.pack(side="left", padx=2)
        self.e_k.insert(0, "2")

        # Symbole *
        tk.Label(frm_mul, text="x", bg=BG2, fg=WARNING,
                 font=("Courier New", 18, "bold")).pack()

        # Point P multiplication
        frm_MP = tk.LabelFrame(frm_mul, text=" Point P a multiplier ",
                               bg=BG3, fg=ACCENT,
                               font=("Courier New", 9, "bold"),
                               relief="flat", bd=1)
        frm_MP.pack(fill="x", padx=10, pady=4)
        r_mp = tk.Frame(frm_MP, bg=BG3)
        r_mp.pack(pady=8)
        tk.Label(r_mp, text="x de P :", bg=BG3, fg=TEXT2,
                 font=("Courier New", 9)).pack(side="left", padx=(10, 4))
        self.e_mpx = tk.Entry(r_mp, bg=BG, fg=ACCENT,
                              font=("Courier New", 10, "bold"),
                              width=8, relief="flat", bd=3,
                              justify="center")
        self.e_mpx.pack(side="left", padx=2)
        self.e_mpx.insert(0, "3")
        tk.Label(r_mp, text="y de P :", bg=BG3, fg=TEXT2,
                 font=("Courier New", 9)).pack(side="left", padx=(16, 4))
        self.e_mpy = tk.Entry(r_mp, bg=BG, fg=ACCENT,
                              font=("Courier New", 10, "bold"),
                              width=8, relief="flat", bd=3,
                              justify="center")
        self.e_mpy.pack(side="left", padx=2)
        self.e_mpy.insert(0, "6")

        # Boutons multiplication
        btn_mul = tk.Frame(frm_mul, bg=BG2)
        btn_mul.pack(pady=8)
        ttk.Button(btn_mul, text="Calculer k * P",
                   command=self._do_mult,
                   style="Green.TButton").pack(side="left", padx=4)
        ttk.Button(btn_mul, text="Remettre a zero",
                   command=self._reset_mul_fields,
                   style="Orange.TButton").pack(side="left", padx=4)
        ttk.Button(btn_mul, text="Utiliser G comme P",
                   command=self._use_G_as_MP).pack(side="left", padx=4)
        ttk.Button(btn_mul, text="Voir points valides",
                   command=self._show_valid_points).pack(side="left", padx=4)

        # Resultat multiplication
        res_mul_f = tk.LabelFrame(frm_mul, text=" Resultat  k * P = ? ",
                                  bg=BG3, fg=SUCCESS,
                                  font=("Courier New", 9, "bold"),
                                  relief="flat", bd=1)
        res_mul_f.pack(fill="x", padx=10, pady=(4, 10))
        self.lbl_mul_result = tk.Label(res_mul_f,
                                       text="(cliquer Calculer)",
                                       bg=BG3, fg=TEXT2,
                                       font=("Courier New", 11, "bold"),
                                       wraplength=260)
        self.lbl_mul_result.pack(pady=10, padx=10)

        # ── JOURNAL en bas ──
        frm_log = tk.LabelFrame(parent,
                                text="  Journal des Operations  ",
                                bg=BG2, fg=ACCENT,
                                font=("Courier New", 9, "bold"),
                                relief="solid", bd=1)
        frm_log.pack(fill="x", padx=8, pady=(4, 6))

        self.txt_log = scrolledtext.ScrolledText(
            frm_log, bg="#04060F", fg=TEXT2,
            font=("Courier New", 9),
            relief="flat", wrap="word", height=5)
        self.txt_log.pack(fill="x", padx=8, pady=6)
        self._add_tags(self.txt_log)

        self._barre_effacer(frm_log, BG2, [
            ("Effacer le journal",
             lambda: self.txt_log.delete("1.0", "end")),
            ("Effacer tous les resultats",  self._reset_ops_results),
            ("Remettre valeurs par defaut", self._reset_ops_fields),
        ])

    # ----------------------------------------------------------
    #  ONGLET 6 : THEORIE
    # ----------------------------------------------------------

    def _tab_about(self):
        parent = self.t_about
        txt = scrolledtext.ScrolledText(
            parent, bg=BG2, fg=TEXT,
            font=("Courier New", 10),
            relief="flat", wrap="word",
            padx=28, pady=16)
        txt.pack(fill="both", expand=True, padx=8, pady=8)
        self._add_tags(txt)

        txt.insert("end", "ECC CRYPTOGRAPHY LAB - THEORIE\n", "accent")
        txt.insert("end", "=" * 54 + "\n\n", "dim")
        txt.insert("end", "1. COURBE ELLIPTIQUE\n", "bold")
        txt.insert("end",
            "\n   y^2 = x^3 + ax + b  (mod p)\n"
            "   Condition : 4a^3 + 27b^2 != 0 (mod p)\n\n")
        txt.insert("end", "2. ADDITION DE POINTS\n", "bold")
        txt.insert("end",
            "\n   P=(x1,y1) + Q=(x2,y2) = R=(x3,y3)\n"
            "   lambda = (y2-y1) / (x2-x1)  mod p\n"
            "   x3 = lambda^2 - x1 - x2     mod p\n"
            "   y3 = lambda*(x1-x3) - y1    mod p\n\n")
        txt.insert("end", "3. MULTIPLICATION SCALAIRE\n", "bold")
        txt.insert("end",
            "\n   k * P = P + P + P + ... (k fois)\n"
            "   Algorithme double-and-add en O(log k)\n\n")
        txt.insert("end", "4. ECDH - ECHANGE DE CLES\n", "bold")
        txt.insert("end",
            "\n   Alice : cle privee dA, cle publique QA = dA * G\n"
            "   Bob   : cle privee dB, cle publique QB = dB * G\n"
            "   Secret partage S = dA*QB = dB*QA\n\n")
        txt.insert("end", "5. CHIFFREMENT HYBRIDE ECC\n", "bold")
        txt.insert("end",
            "\n   1. k aleatoire, C1 = k*G (point ephemere)\n"
            "   2. Secret S = k * Q_destinataire\n"
            "   3. Cle = SHA256(S)  (32 octets)\n"
            "   4. Message_chiffre = Message XOR Cle\n"
            "   5. Envoyer (C1, Message_chiffre)\n\n"
            "   Dechiffrement :\n"
            "   1. S = d * C1  (meme secret)\n"
            "   2. Cle = SHA256(S)\n"
            "   3. Message = Message_chiffre XOR Cle\n\n")
        txt.insert("end", "6. ECDSA - SIGNATURE\n", "bold")
        txt.insert("end",
            "\n   Signature (r,s) : R=k*G, r=Rx mod n\n"
            "   s = k^-1*(hash(m) + r*d) mod n\n"
            "   Verification : u1*G + u2*Q doit donner r\n\n")
        txt.insert("end",
            "  Application educative - Python + Tkinter\n",
            "warning")
        txt.configure(state="disabled")


    # ----------------------------------------------------------
    #  ONGLET 7 : COMMUNICATION COMPLETE
    #  Flux reel : ECDH + Chiffrement + Signature en un seul onglet
    # ----------------------------------------------------------

    def _tab_communication(self):
        import tkinter.scrolledtext as scrolledtext
        parent = self.t_comms

        # ── Variables internes ────────────────────────────────────
        self._cc_send_priv_val = None
        self._cc_send_pub_val  = None
        self._cc_recv_priv_val = None
        self._cc_recv_pub_val  = None
        self._cc_sig_priv_val  = None
        self._cc_sig_pub_val   = None
        self._cc_signature_val = None
        self._cc_enc_C1        = None
        self._cc_enc_bytes     = None
        self._rx_bob_priv_val  = None
        self._rx_bob_pub_val   = None
        sv = tk.StringVar
        self._cc_sv_send_priv = sv(value="")
        self._cc_sv_send_pub  = sv(value="(pas encore calcule)")
        self._cc_sv_recv_priv = sv(value="")
        self._cc_sv_recv_pub  = sv(value="(pas encore calcule)")
        self._cc_sv_sig_priv  = sv(value="")
        self._cc_sv_sig_pub   = sv(value="(pas encore calcule)")
        self._cc_sv_secret_s  = sv(value="")
        self._cc_sv_secret_r  = sv(value="")
        self._cc_sv_sig_r     = sv(value="--")
        self._cc_sv_sig_s     = sv(value="--")

        # ── Conteneur principal ───────────────────────────────────
        # On empile : écran de choix + panneau chiffrement + panneau déchiffrement
        # Un seul visible à la fois

        # ── ECRAN 1 : CHOIX PRINCIPAL ────────────────────────────
        self._cc_choice_frame = tk.Frame(parent, bg=BG)
        self._cc_choice_frame.pack(fill="both", expand=True)

        tk.Label(self._cc_choice_frame,
                 text="COMMUNICATION COMPLETE",
                 bg=BG, fg=ACCENT,
                 font=("Courier New", 16, "bold")).pack(pady=(50, 4))
        tk.Label(self._cc_choice_frame,
                 text="ECDH  +  Chiffrement  +  Signature  ECDSA",
                 bg=BG, fg=TEXT2,
                 font=("Courier New", 10, "italic")).pack(pady=(0, 50))

        btn_row = tk.Frame(self._cc_choice_frame, bg=BG)
        btn_row.pack(pady=10)

        def make_main_btn(parent, bg_col, fg_col, title, subtitle, cmd):
            f = tk.Frame(parent, bg=bg_col, relief="solid", bd=2, cursor="hand2")
            f.pack(side="left", padx=30)
            tk.Label(f, text=title, bg=bg_col, fg=fg_col,
                     font=("Courier New", 14, "bold"),
                     cursor="hand2").pack(padx=30, pady=8)
            tk.Label(f, text=subtitle, bg=bg_col, fg=TEXT2,
                     font=("Courier New", 9), justify="center",
                     cursor="hand2").pack(padx=20, pady=(0, 14))
            f.bind("<Button-1>", lambda e: cmd())
            for w in f.winfo_children():
                w.bind("<Button-1>", lambda e: cmd())

        make_main_btn(btn_row, "#003020", SUCCESS,
                      "  CHIFFREMENT  ",
                      "Expediteur (Alice)\nchiffre et/ou signe\nun message pour Bob",
                      lambda: self._cc_show_panel("sub_enc"))

        make_main_btn(btn_row, "#200030", "#B39DDB",
                      "  DECHIFFREMENT  ",
                      "Destinataire (Bob)\ndechiffre et/ou verifie\nun message recu",
                      lambda: self._cc_show_panel("sub_dec"))

        # ── ECRAN 2a : SOUS-CHOIX CHIFFREMENT ────────────────────
        self._cc_sub_enc_frame = tk.Frame(parent, bg=BG)

        tk.Label(self._cc_sub_enc_frame,
                 text="CHIFFREMENT",
                 bg=BG, fg=SUCCESS,
                 font=("Courier New", 16, "bold")).pack(pady=(40, 4))
        tk.Label(self._cc_sub_enc_frame,
                 text="Choisir l'ordre des operations :",
                 bg=BG, fg=TEXT2,
                 font=("Courier New", 10, "italic")).pack(pady=(0, 30))

        sub_enc_row = tk.Frame(self._cc_sub_enc_frame, bg=BG)
        sub_enc_row.pack(pady=10)

        def make_sub_btn(parent, bg_col, fg_col, line1, line2, expl, cmd):
            f = tk.Frame(parent, bg=bg_col, relief="solid", bd=2, cursor="hand2")
            f.pack(side="left", padx=20)
            tk.Label(f, text=line1, bg=bg_col, fg=fg_col,
                     font=("Courier New", 12, "bold"),
                     cursor="hand2").pack(padx=24, pady=(10, 2))
            tk.Label(f, text=line2, bg=bg_col, fg=fg_col,
                     font=("Courier New", 10),
                     cursor="hand2").pack(padx=24, pady=(0, 6))
            tk.Label(f, text=expl, bg=bg_col, fg=TEXT2,
                     font=("Courier New", 8, "italic"), justify="center",
                     cursor="hand2").pack(padx=16, pady=(0, 14))
            f.bind("<Button-1>", lambda e: cmd())
            for w in f.winfo_children():
                w.bind("<Button-1>", lambda e: cmd())

        make_sub_btn(sub_enc_row, "#001A0F", SUCCESS,
                     "1. CHIFFRER",
                     "2. SIGNER",
                     "Chiffrer d'abord,\npuis signer le\nmessage chiffre",
                     lambda: self._cc_set_mode_and_show("chiffrer_puis_signer", "enc"))

        make_sub_btn(sub_enc_row, "#001A20", "#00D4FF",
                     "1. SIGNER",
                     "2. CHIFFRER",
                     "Signer d'abord,\npuis chiffrer le\nmessage signe",
                     lambda: self._cc_set_mode_and_show("signer_puis_chiffrer", "enc"))

        ttk.Button(self._cc_sub_enc_frame, text="< Retour au menu",
                   command=lambda: self._cc_show_panel("menu")).pack(pady=16)

        # ── ECRAN 2b : SOUS-CHOIX DECHIFFREMENT ──────────────────
        self._cc_sub_dec_frame = tk.Frame(parent, bg=BG)

        tk.Label(self._cc_sub_dec_frame,
                 text="DECHIFFREMENT",
                 bg=BG, fg="#B39DDB",
                 font=("Courier New", 16, "bold")).pack(pady=(40, 4))
        tk.Label(self._cc_sub_dec_frame,
                 text="Choisir l'ordre des operations :",
                 bg=BG, fg=TEXT2,
                 font=("Courier New", 10, "italic")).pack(pady=(0, 30))

        sub_dec_row = tk.Frame(self._cc_sub_dec_frame, bg=BG)
        sub_dec_row.pack(pady=10)

        make_sub_btn(sub_dec_row, "#150025", "#B39DDB",
                     "1. DECHIFFRER",
                     "2. VERIFIER",
                     "Dechiffrer le message\nd'abord, puis verifier\nla signature",
                     lambda: self._cc_set_mode_and_show("dechiffrer_puis_verifier", "dec"))

        make_sub_btn(sub_dec_row, "#0A001A", "#9575CD",
                     "1. VERIFIER",
                     "2. DECHIFFRER",
                     "Verifier la signature\nd'abord, puis\ndechiffrer",
                     lambda: self._cc_set_mode_and_show("verifier_puis_dechiffrer", "dec"))

        ttk.Button(self._cc_sub_dec_frame, text="< Retour au menu",
                   command=lambda: self._cc_show_panel("menu")).pack(pady=16)

        # ── PANNEAUX OPERATIONNELS (caches au depart) ────────────
        self._cc_enc_panel = tk.Frame(parent, bg=BG)
        self._cc_build_enc_panel(self._cc_enc_panel, scrolledtext)

        self._cc_dec_panel = tk.Frame(parent, bg=BG)
        self._cc_build_dec_panel(self._cc_dec_panel, scrolledtext)

        # Mode courant
        self._cc_mode = "chiffrer_puis_signer"

    def _cc_show_panel(self, which):
        """Affiche le panneau demande, cache tous les autres."""
        for f in [self._cc_choice_frame, self._cc_sub_enc_frame,
                  self._cc_sub_dec_frame, self._cc_enc_panel, self._cc_dec_panel]:
            f.pack_forget()
        if which == "sub_enc":
            self._cc_sub_enc_frame.pack(fill="both", expand=True)
        elif which == "sub_dec":
            self._cc_sub_dec_frame.pack(fill="both", expand=True)
        elif which == "enc":
            self._cc_enc_panel.pack(fill="both", expand=True)
        elif which == "dec":
            self._cc_dec_panel.pack(fill="both", expand=True)
        else:  # "menu"
            self._cc_choice_frame.pack(fill="both", expand=True)

    def _cc_set_mode_and_show(self, mode, panel):
        """Enregistre le mode choisi et affiche le panneau correspondant."""
        self._cc_mode = mode
        self._cc_show_panel(panel)
        # Mettre a jour le bandeau de mode dans le panneau
        try:
            if panel == "enc":
                if mode == "chiffrer_puis_signer":
                    self._cc_mode_lbl_enc.config(
                        text="Mode : CHIFFRER puis SIGNER  |  "
                             "Le message est d'abord chiffre, puis la signature est apposee")
                else:
                    self._cc_mode_lbl_enc.config(
                        text="Mode : SIGNER puis CHIFFRER  |  "
                             "Le message est d'abord signe, puis le tout est chiffre")
            else:
                if mode == "dechiffrer_puis_verifier":
                    self._cc_mode_lbl_dec.config(
                        text="Mode : DECHIFFRER puis VERIFIER  |  "
                             "Le message est dechiffre, puis la signature est verifiee")
                else:
                    self._cc_mode_lbl_dec.config(
                        text="Mode : VERIFIER puis DECHIFFRER  |  "
                             "La signature est d'abord verifiee, puis le message est dechiffre")
        except Exception:
            pass

    def _cc_build_enc_panel(self, parent, scrolledtext):
        """Construit le panneau CHIFFREMENT : Alice | Reseau | Bob."""

        def sec(p, t, fg=ACCENT, bg=BG2):
            tk.Label(p, text=t, bg=bg, fg=fg,
                     font=("Courier New", 9, "bold")).pack(
                     anchor="w", padx=8, pady=(8, 2))

        def erow(p, lbl, var, fg=ACCENT2, ro=False, bg=BG2):
            r = tk.Frame(p, bg=bg)
            r.pack(fill="x", padx=8, pady=2)
            tk.Label(r, text=lbl, bg=bg, fg=TEXT2,
                     font=("Courier New", 9), width=12,
                     anchor="w").pack(side="left")
            e = tk.Entry(r, bg=BG3, fg=fg,
                         font=("Courier New", 9),
                         insertbackground=ACCENT,
                         relief="flat", bd=2,
                         textvariable=var,
                         state="readonly" if ro else "normal")
            e.pack(side="left", fill="x", expand=True)
            return e

        # En-tete
        hdr = tk.Frame(parent, bg=BG4)
        hdr.pack(fill="x", padx=6, pady=(4, 2))
        ttk.Button(hdr, text="< Retour",
                   command=lambda: self._cc_show_panel("sub_enc")).pack(
                   side="left", padx=6, pady=3)
        tk.Label(hdr,
                 text="CHIFFREMENT  --  Alice envoie un message chiffre a Bob",
                 bg=BG4, fg=SUCCESS,
                 font=("Courier New", 9, "bold")).pack(side="left", pady=4)
        ttk.Button(hdr, text="DEMO AUTO",
                   command=self._cc_demo_auto,
                   style="Green.TButton").pack(side="right", padx=4, pady=3)
        ttk.Button(hdr, text="Reinitialiser",
                   command=self._cc_reset,
                   style="Orange.TButton").pack(side="right", padx=2, pady=3)

        # Bandeau mode
        mode_bar = tk.Frame(parent, bg="#001A10")
        mode_bar.pack(fill="x", padx=6, pady=(0, 2))
        self._cc_mode_lbl_enc = tk.Label(mode_bar,
                 text="Mode : CHIFFRER puis SIGNER  |  Le message est d'abord chiffre, puis la signature est apposee",
                 bg="#001A10", fg=SUCCESS,
                 font=("Courier New", 8, "italic"))
        self._cc_mode_lbl_enc.pack(side="left", padx=8, pady=3)
        ttk.Button(mode_bar, text="Changer d'ordre",
                   command=lambda: self._cc_show_panel("sub_enc"),
                   style="Green.TButton").pack(side="right", padx=6, pady=2)

        # 3 colonnes
        cols = tk.Frame(parent, bg=BG)
        cols.pack(fill="both", expand=True, padx=6, pady=2)
        cols.columnconfigure(0, weight=3)
        cols.columnconfigure(1, weight=4)
        cols.columnconfigure(2, weight=3)

        # ── ALICE ────────────────────────────────────────────────
        c_alice = tk.LabelFrame(cols, text="  ALICE  (Expediteur)  ",
                                bg=BG2, fg="#00E5FF",
                                font=("Courier New", 10, "bold"),
                                relief="solid", bd=2)
        c_alice.grid(row=0, column=0, sticky="nsew", padx=(0, 3), pady=2)

        sec(c_alice, "Cles ECDH + Signature", "#00E5FF")
        erow(c_alice, "d prive :", self._cc_sv_send_priv, ACCENT2)
        erow(c_alice, "Q public :", self._cc_sv_send_pub, SUCCESS, ro=True)
        erow(c_alice, "d sign :", self._cc_sv_sig_priv, ACCENT2)
        erow(c_alice, "Q sign :", self._cc_sv_sig_pub, SUCCESS, ro=True)
        tk.Label(c_alice, text="  Saisir d ou Generer",
                 bg=BG2, fg=TEXT2,
                 font=("Courier New", 8, "italic")).pack(anchor="w", padx=8)
        bf1 = tk.Frame(c_alice, bg=BG2)
        bf1.pack(pady=4)
        ttk.Button(bf1, text="Generer",
                   command=self._cc_gen_sender).pack(side="left", padx=3)
        ttk.Button(bf1, text="Calc Q",
                   command=self._cc_calc_sender_manual,
                   style="Green.TButton").pack(side="left", padx=3)

        tk.Frame(c_alice, bg=BG3, height=1).pack(fill="x", padx=8, pady=5)

        sec(c_alice, "Message a envoyer", WARNING)
        mf = tk.Frame(c_alice, bg=BG2)
        mf.pack(fill="x", padx=8, pady=2)
        self._cc_ent_msg = tk.Entry(mf, bg=BG3, fg=TEXT,
                                    font=("Courier New", 10),
                                    insertbackground=ACCENT,
                                    relief="flat", bd=3)
        self._cc_ent_msg.pack(fill="x")
        self._cc_ent_msg.insert(0, "Rendez-vous a 18h !")
        ttk.Button(c_alice, text="CHIFFRER + SIGNER",
                   command=self._cc_chiffrer_signer,
                   style="Green.TButton").pack(pady=6)

        tk.Frame(c_alice, bg=BG3, height=1).pack(fill="x", padx=8, pady=5)

        sec(c_alice, "Signature produite (r, s)", SUCCESS)
        erow(c_alice, "r =", self._cc_sv_sig_r, SUCCESS, ro=True)
        erow(c_alice, "s =", self._cc_sv_sig_s, SUCCESS, ro=True)
        tk.Label(c_alice,
                 text="  Seul Alice peut produire\n  cette signature",
                 bg=BG2, fg=TEXT2,
                 font=("Courier New", 8, "italic"),
                 justify="left").pack(anchor="w", padx=8, pady=(2, 8))

        # ── RESEAU PUBLIC ────────────────────────────────────────
        c_net = tk.LabelFrame(cols,
                              text="  RESEAU PUBLIC  --  Visible par TOUT LE MONDE  ",
                              bg="#08080F", fg=WARNING,
                              font=("Courier New", 9, "bold"),
                              relief="solid", bd=2)
        c_net.grid(row=0, column=1, sticky="nsew", padx=3, pady=2)

        tk.Label(c_net, text="Cles publiques echangees :",
                 bg="#08080F", fg=TEXT2,
                 font=("Courier New", 8)).pack(anchor="w", padx=8, pady=(6, 2))
        net_k = tk.Frame(c_net, bg="#0F0F1A")
        net_k.pack(fill="x", padx=6, pady=(0, 4))
        self._net_q_send = tk.Label(net_k, text="Q Alice (ECDH)  : (en attente)",
                 bg="#0F0F1A", fg="#00E5FF",
                 font=("Courier New", 8), wraplength=250, justify="left")
        self._net_q_send.pack(anchor="w", padx=8, pady=2)
        self._net_q_recv = tk.Label(net_k, text="Q Bob   (ECDH)  : (en attente)",
                 bg="#0F0F1A", fg="#B39DDB",
                 font=("Courier New", 8), wraplength=250, justify="left")
        self._net_q_recv.pack(anchor="w", padx=8, pady=2)
        self._net_q_sig = tk.Label(net_k, text="Q Alice (sign)  : (en attente)",
                 bg="#0F0F1A", fg=SUCCESS,
                 font=("Courier New", 8), wraplength=250, justify="left")
        self._net_q_sig.pack(anchor="w", padx=8, pady=(2, 6))

        net_m = tk.LabelFrame(c_net,
                              text="  Message intercepte -- ILLISIBLE  ",
                              bg="#0A0A0F", fg=WARNING,
                              font=("Courier New", 8, "bold"),
                              relief="solid", bd=1)
        net_m.pack(fill="both", expand=True, padx=6, pady=(0, 4))

        tk.Label(net_m, text="Point ephemere C1 :",
                 bg="#0A0A0F", fg=TEXT2,
                 font=("Courier New", 8)).pack(anchor="w", padx=8, pady=(6, 0))
        self._net_c1 = tk.Label(net_m, text="(en attente...)",
                 bg="#0A0A0F", fg=ACCENT,
                 font=("Courier New", 8), wraplength=250, justify="left")
        self._net_c1.pack(anchor="w", padx=8, pady=(0, 4))

        tk.Label(net_m, text="Octets chiffres (hex) :",
                 bg="#0A0A0F", fg=TEXT2,
                 font=("Courier New", 8)).pack(anchor="w", padx=8)
        self._net_hex = scrolledtext.ScrolledText(net_m,
                 bg="#020208", fg=WARNING,
                 font=("Courier New", 8), height=3,
                 relief="flat", wrap="word", state="disabled")
        self._net_hex.pack(fill="x", padx=8, pady=(2, 4))

        tk.Label(net_m, text="Signature (r, s) :",
                 bg="#0A0A0F", fg=TEXT2,
                 font=("Courier New", 8)).pack(anchor="w", padx=8)
        self._net_sig_lbl = tk.Label(net_m, text="(en attente...)",
                 bg="#0A0A0F", fg=SUCCESS,
                 font=("Courier New", 8), wraplength=250, justify="left")
        self._net_sig_lbl.pack(anchor="w", padx=8, pady=(0, 4))

        intru_f = tk.Frame(c_net, bg="#150505")
        intru_f.pack(fill="x", padx=6, pady=(0, 6))
        self._net_intru = tk.Label(intru_f,
                 text="Personne A : essaie de dechiffrer... ECHEC\n"
                      "Personne B : essaie de forger sign... ECHEC\n"
                      "Seul Bob (cle privee) peut dechiffrer !",
                 bg="#150505", fg=ERROR,
                 font=("Courier New", 8), justify="left")
        self._net_intru.pack(anchor="w", padx=8, pady=6)

        # ── BOB ──────────────────────────────────────────────────
        c_bob = tk.LabelFrame(cols, text="  BOB  (Destinataire)  ",
                              bg=BG2, fg="#B39DDB",
                              font=("Courier New", 10, "bold"),
                              relief="solid", bd=2)
        c_bob.grid(row=0, column=2, sticky="nsew", padx=(3, 0), pady=2)

        sec(c_bob, "Cles ECDH de Bob", "#B39DDB")
        erow(c_bob, "d prive :", self._cc_sv_recv_priv, ACCENT2)
        erow(c_bob, "Q public :", self._cc_sv_recv_pub, SUCCESS, ro=True)
        tk.Label(c_bob, text="  Saisir d ou Generer",
                 bg=BG2, fg=TEXT2,
                 font=("Courier New", 8, "italic")).pack(anchor="w", padx=8)
        bf2 = tk.Frame(c_bob, bg=BG2)
        bf2.pack(pady=4)
        ttk.Button(bf2, text="Generer",
                   command=self._cc_gen_receiver).pack(side="left", padx=3)
        ttk.Button(bf2, text="Calc Q",
                   command=self._cc_calc_receiver_manual,
                   style="Green.TButton").pack(side="left", padx=3)

        tk.Frame(c_bob, bg=BG3, height=1).pack(fill="x", padx=8, pady=5)

        sec(c_bob, "Secret partage ECDH", ACCENT)
        erow(c_bob, "S Alice :", self._cc_sv_secret_s, ACCENT, ro=True)
        erow(c_bob, "S Bob :", self._cc_sv_secret_r, ACCENT, ro=True)
        tk.Label(c_bob, text="  Les deux S doivent coincider",
                 bg=BG2, fg=TEXT2,
                 font=("Courier New", 8, "italic")).pack(anchor="w", padx=8)
        ttk.Button(c_bob, text="Calculer secret",
                   command=self._cc_calculer_secret).pack(pady=4)

        tk.Frame(c_bob, bg=BG3, height=1).pack(fill="x", padx=8, pady=5)

        sec(c_bob, "Dechiffrement + Verification", "#B39DDB")
        ttk.Button(c_bob, text="DECHIFFRER + VERIFIER",
                   command=self._cc_dechiffrer_verifier,
                   style="Green.TButton").pack(padx=8, pady=4)

        self._cc_txt_resultat = scrolledtext.ScrolledText(
                c_bob, bg="#030F03", fg=SUCCESS,
                font=("Courier New", 9), height=6,
                relief="flat", wrap="word", state="disabled")
        self._cc_txt_resultat.pack(fill="both", expand=True, padx=8, pady=(0, 8))
        self._add_tags(self._cc_txt_resultat)

    def _cc_build_dec_panel(self, parent, scrolledtext):
        """Construit le panneau DECHIFFREMENT : Bob colle les donnees recues d'Alice."""

        # En-tete
        hdr = tk.Frame(parent, bg=BG4)
        hdr.pack(fill="x", padx=6, pady=(4, 2))
        ttk.Button(hdr, text="< Retour",
                   command=lambda: self._cc_show_panel("sub_dec")).pack(
                   side="left", padx=6, pady=3)
        tk.Label(hdr,
                 text="DECHIFFREMENT  --  Bob lit un message recu d'Alice",
                 bg=BG4, fg="#B39DDB",
                 font=("Courier New", 9, "bold")).pack(side="left", pady=4)
        ttk.Button(hdr, text="Tout effacer",
                   command=self._rx_reset,
                   style="Orange.TButton").pack(side="right", padx=6, pady=3)

        # Bandeau mode
        mode_bar2 = tk.Frame(parent, bg="#150025")
        mode_bar2.pack(fill="x", padx=6, pady=(0, 2))
        self._cc_mode_lbl_dec = tk.Label(mode_bar2,
                 text="Mode : DECHIFFRER puis VERIFIER  |  Le message est dechiffre, puis la signature est verifiee",
                 bg="#150025", fg="#B39DDB",
                 font=("Courier New", 8, "italic"))
        self._cc_mode_lbl_dec.pack(side="left", padx=8, pady=3)
        ttk.Button(mode_bar2, text="Changer d'ordre",
                   command=lambda: self._cc_show_panel("sub_dec"),
                   style="Orange.TButton").pack(side="right", padx=6, pady=2)

        tk.Label(parent,
                 text="  Alice peut etre n'importe ou dans le monde. "
                      "Elle envoie les donnees ci-dessous par email ou autre moyen. "
                      "Bob les colle ici et dechiffre.",
                 bg=BG, fg=TEXT2,
                 font=("Courier New", 8, "italic"),
                 wraplength=900, justify="left").pack(
                 anchor="w", padx=10, pady=(0, 4))

        # Deux colonnes : formulaire | resultat
        cols = tk.Frame(parent, bg=BG)
        cols.pack(fill="both", expand=True, padx=6, pady=2)
        cols.columnconfigure(0, weight=5)
        cols.columnconfigure(1, weight=3)

        # ── GAUCHE : formulaire ──────────────────────────────────
        c_form = tk.Frame(cols, bg=BG)
        c_form.grid(row=0, column=0, sticky="nsew", padx=(0, 4))

        # Cle privee de Bob
        frm_bob = tk.LabelFrame(c_form, text="  MA CLE PRIVEE (Bob)  ",
                                bg=BG, fg="#B39DDB",
                                font=("Courier New", 9, "bold"),
                                relief="solid", bd=1)
        frm_bob.pack(fill="x", pady=(0, 6))

        rk = tk.Frame(frm_bob, bg=BG)
        rk.pack(fill="x", padx=8, pady=4)
        rk.columnconfigure(1, weight=1)
        rk.columnconfigure(3, weight=1)
        tk.Label(rk, text="d prive :", bg=BG, fg=TEXT2,
                 font=("Courier New", 9)).grid(row=0, column=0, sticky="w", padx=(0, 4))
        self._rx_bob_priv = tk.Entry(rk, bg=BG3, fg=ACCENT2,
                                     font=("Courier New", 9),
                                     insertbackground=ACCENT,
                                     relief="flat", bd=3)
        self._rx_bob_priv.grid(row=0, column=1, padx=4, sticky="ew")
        tk.Label(rk, text="  Q public :", bg=BG, fg=TEXT2,
                 font=("Courier New", 9)).grid(row=0, column=2, sticky="w", padx=(8, 4))
        self._rx_bob_pub_lbl = tk.Label(rk,
                 text="(pas encore calcule)",
                 bg=BG3, fg=SUCCESS,
                 font=("Courier New", 9))
        self._rx_bob_pub_lbl.grid(row=0, column=3, padx=4, sticky="ew")

        bf = tk.Frame(frm_bob, bg=BG)
        bf.pack(anchor="w", padx=8, pady=(0, 6))
        ttk.Button(bf, text="Generer cle Bob",
                   command=self._rx_gen_bob).pack(side="left", padx=3)
        ttk.Button(bf, text="Calculer Q depuis d",
                   command=self._rx_calc_bob,
                   style="Green.TButton").pack(side="left", padx=3)
        tk.Label(frm_bob,
                 text="  Partager Q public avec Alice pour qu'elle chiffre !",
                 bg=BG, fg=TEXT2,
                 font=("Courier New", 8, "italic")).pack(anchor="w", padx=8, pady=(0, 4))

        # Donnees recues d'Alice
        frm_rx = tk.LabelFrame(c_form,
                               text="  DONNEES RECUES D'ALICE  (coller ici)  ",
                               bg=BG, fg="#00E5FF",
                               font=("Courier New", 9, "bold"),
                               relief="solid", bd=1)
        frm_rx.pack(fill="x", pady=(0, 6))

        # C1
        tk.Label(frm_rx, text="Point ephemere C1 (x, y) :",
                 bg=BG, fg=ACCENT2,
                 font=("Courier New", 9, "bold")).pack(
                 anchor="w", padx=8, pady=(6, 0))
        c1_row = tk.Frame(frm_rx, bg=BG)
        c1_row.pack(fill="x", padx=8, pady=(2, 4))
        tk.Label(c1_row, text="x =", bg=BG, fg=TEXT2,
                 font=("Courier New", 9)).pack(side="left")
        self._rx_c1x = tk.Entry(c1_row, bg=BG3, fg=ACCENT,
                                font=("Courier New", 9),
                                insertbackground=ACCENT,
                                relief="flat", bd=3, width=14)
        self._rx_c1x.pack(side="left", padx=4)
        tk.Label(c1_row, text="y =", bg=BG, fg=TEXT2,
                 font=("Courier New", 9)).pack(side="left", padx=(12, 0))
        self._rx_c1y = tk.Entry(c1_row, bg=BG3, fg=ACCENT,
                                font=("Courier New", 9),
                                insertbackground=ACCENT,
                                relief="flat", bd=3, width=14)
        self._rx_c1y.pack(side="left", padx=4)

        # Hex
        tk.Label(frm_rx, text="Octets chiffres (hexadecimal) :",
                 bg=BG, fg=ACCENT2,
                 font=("Courier New", 9, "bold")).pack(
                 anchor="w", padx=8, pady=(4, 0))
        tk.Label(frm_rx, text="  ex: 3a f2 09 c1 8b...",
                 bg=BG, fg=TEXT2,
                 font=("Courier New", 7, "italic")).pack(
                 anchor="w", padx=8, pady=(0, 2))
        self._rx_hex = scrolledtext.ScrolledText(frm_rx, bg=BG3, fg=WARNING,
                         font=("Courier New", 9), height=3,
                         relief="flat", wrap="word")
        self._rx_hex.pack(fill="x", padx=8, pady=(0, 4))

        # Signature
        tk.Label(frm_rx, text="Signature d'Alice (r, s) :",
                 bg=BG, fg=ACCENT2,
                 font=("Courier New", 9, "bold")).pack(
                 anchor="w", padx=8, pady=(4, 0))
        rs_row = tk.Frame(frm_rx, bg=BG)
        rs_row.pack(fill="x", padx=8, pady=(2, 4))
        tk.Label(rs_row, text="r =", bg=BG, fg=TEXT2,
                 font=("Courier New", 9)).pack(side="left")
        self._rx_sig_r = tk.Entry(rs_row, bg=BG3, fg=SUCCESS,
                                  font=("Courier New", 9),
                                  insertbackground=ACCENT,
                                  relief="flat", bd=3, width=16)
        self._rx_sig_r.pack(side="left", padx=4)
        tk.Label(rs_row, text="s =", bg=BG, fg=TEXT2,
                 font=("Courier New", 9)).pack(side="left", padx=(12, 0))
        self._rx_sig_s = tk.Entry(rs_row, bg=BG3, fg=SUCCESS,
                                  font=("Courier New", 9),
                                  insertbackground=ACCENT,
                                  relief="flat", bd=3, width=16)
        self._rx_sig_s.pack(side="left", padx=4)

        # Q Alice
        tk.Label(frm_rx, text="Cle publique Q d'Alice (pour verifier) :",
                 bg=BG, fg=ACCENT2,
                 font=("Courier New", 9, "bold")).pack(
                 anchor="w", padx=8, pady=(4, 0))
        qa_row = tk.Frame(frm_rx, bg=BG)
        qa_row.pack(fill="x", padx=8, pady=(2, 8))
        tk.Label(qa_row, text="x =", bg=BG, fg=TEXT2,
                 font=("Courier New", 9)).pack(side="left")
        self._rx_qax = tk.Entry(qa_row, bg=BG3, fg="#00E5FF",
                                font=("Courier New", 9),
                                insertbackground=ACCENT,
                                relief="flat", bd=3, width=14)
        self._rx_qax.pack(side="left", padx=4)
        tk.Label(qa_row, text="y =", bg=BG, fg=TEXT2,
                 font=("Courier New", 9)).pack(side="left", padx=(12, 0))
        self._rx_qay = tk.Entry(qa_row, bg=BG3, fg="#00E5FF",
                                font=("Courier New", 9),
                                insertbackground=ACCENT,
                                relief="flat", bd=3, width=14)
        self._rx_qay.pack(side="left", padx=4)

        # Bouton
        ttk.Button(c_form,
                   text="  DECHIFFRER + VERIFIER LA SIGNATURE  ",
                   command=self._rx_dechiffrer,
                   style="Green.TButton").pack(pady=8)

        # ── DROITE : resultat ─────────────────────────────────────
        c_res = tk.LabelFrame(cols, text="  MESSAGE DECHIFFRE  ",
                              bg=BG2, fg=SUCCESS,
                              font=("Courier New", 9, "bold"),
                              relief="solid", bd=2)
        c_res.grid(row=0, column=1, sticky="nsew", pady=2)

        tk.Label(c_res,
                 text="Message lu par Bob\napres dechiffrement :",
                 bg=BG2, fg=TEXT2,
                 font=("Courier New", 8, "italic"),
                 justify="left").pack(anchor="w", padx=8, pady=(8, 4))

        self._rx_txt_result = scrolledtext.ScrolledText(
                c_res, bg="#030F03", fg=SUCCESS,
                font=("Courier New", 12, "bold"),
                height=8, relief="flat", wrap="word",
                state="disabled")
        self._rx_txt_result.pack(fill="both", expand=True, padx=8, pady=(0, 8))
        self._add_tags(self._rx_txt_result)


    def _cc_pub_str(self, pt):
        if pt is None:
            return "(pas encore calcule)"
        x, y = pt
        return "(" + (hex(x) if x > 9999 else str(x)) + ", " + (hex(y) if y > 9999 else str(y)) + ")"

    def _cc_update_network(self):
        try:
            self._net_q_send.config(text="Q Alice (ECDH)  : " + self._cc_pub_str(self._cc_send_pub_val))
            self._net_q_recv.config(text="Q Bob   (ECDH)  : " + self._cc_pub_str(self._cc_recv_pub_val))
            self._net_q_sig.config(text="Q Alice (sign)  : " + self._cc_pub_str(self._cc_sig_pub_val))
            if self._cc_enc_C1 and self._cc_enc_bytes:
                self._net_c1.config(text=self._cc_pub_str(self._cc_enc_C1))
                self._net_hex.config(state="normal")
                self._net_hex.delete("1.0", "end")
                h = self._cc_enc_bytes.hex()
                self._net_hex.insert("end", " ".join(h[i:i+2] for i in range(0, len(h), 2)))
                self._net_hex.config(state="disabled")
                if self._cc_signature_val:
                    r, s = self._cc_signature_val
                    self._net_sig_lbl.config(
                        text="r = " + (hex(r) if r > 9999 else str(r)) +
                             "\ns = " + (hex(s) if s > 9999 else str(s)))
                msg = self._cc_ent_msg.get().strip() if hasattr(self, "_cc_ent_msg") else "?"
                n = len(msg)
                self._net_intru.config(
                    text="Personne A : " + ("?" * n) + "  -- ECHEC\n" +
                         "Personne B : " + ("?" * n) + "  -- ECHEC\n" +
                         "Personne C : force brute...  -- ECHEC\n" +
                         "Seul le destinataire (cle privee) peut lire !")
        except Exception:
            pass

    def _cc_gen_sender(self):
        if not self.cipher or not self.ecdsa:
            messagebox.showerror("Erreur", "Aucune courbe chargee.")
            return
        try:
            d_e, q_e = self.cipher.generate_keypair()
            self._cc_send_priv_val = d_e
            self._cc_send_pub_val  = q_e
            self._cc_sv_send_priv.set(str(d_e))
            self._cc_sv_send_pub.set(self._cc_pub_str(q_e))
            d_s, q_s = self.ecdsa.generate_keypair()
            self._cc_sig_priv_val = d_s
            self._cc_sig_pub_val  = q_s
            self._cc_sv_sig_priv.set(str(d_s))
            self._cc_sv_sig_pub.set(self._cc_pub_str(q_s))
            self._cc_sv_sig_r.set("--")
            self._cc_sv_sig_s.set("--")
            self._cc_enc_C1 = None
            self._cc_enc_bytes = None
            self._cc_signature_val = None
            self._cc_update_network()
        except Exception as e:
            messagebox.showerror("Erreur", str(e))

    def _cc_calc_sender_manual(self):
        raw = self._cc_sv_send_priv.get().strip()
        if not raw or not raw.isdigit():
            messagebox.showwarning("Attention", "Entrer un entier d.\nEx: 3 ou 7")
            return
        try:
            d = int(raw)
            if d < 1 or d >= self.n:
                messagebox.showerror("Erreur", "d doit etre entre 1 et " + str(self.n - 1))
                return
            q = self.curve.scalar_mult(d, self.G)
            self._cc_send_priv_val = d
            self._cc_send_pub_val  = q
            self._cc_sv_send_pub.set(self._cc_pub_str(q))
            self._cc_sig_priv_val = d
            self._cc_sig_pub_val  = q
            self._cc_sv_sig_priv.set(str(d))
            self._cc_sv_sig_pub.set(self._cc_pub_str(q))
            self._cc_update_network()
        except Exception as e:
            messagebox.showerror("Erreur", str(e))

    def _cc_gen_receiver(self):
        if not self.cipher:
            messagebox.showerror("Erreur", "Aucune courbe chargee.")
            return
        try:
            d_r, q_r = self.cipher.generate_keypair()
            self._cc_recv_priv_val = d_r
            self._cc_recv_pub_val  = q_r
            self._cc_sv_recv_priv.set(str(d_r))
            self._cc_sv_recv_pub.set(self._cc_pub_str(q_r))
            self._cc_sv_secret_s.set("")
            self._cc_sv_secret_r.set("")
            self._cc_update_network()
        except Exception as e:
            messagebox.showerror("Erreur", str(e))

    def _cc_calc_receiver_manual(self):
        raw = self._cc_sv_recv_priv.get().strip()
        if not raw or not raw.isdigit():
            messagebox.showwarning("Attention", "Entrer un entier d.\nEx: 5 ou 9")
            return
        try:
            d = int(raw)
            if d < 1 or d >= self.n:
                messagebox.showerror("Erreur", "d doit etre entre 1 et " + str(self.n - 1))
                return
            q = self.curve.scalar_mult(d, self.G)
            self._cc_recv_priv_val = d
            self._cc_recv_pub_val  = q
            self._cc_sv_recv_pub.set(self._cc_pub_str(q))
            self._cc_sv_secret_s.set("")
            self._cc_sv_secret_r.set("")
            self._cc_update_network()
        except Exception as e:
            messagebox.showerror("Erreur", str(e))

    def _cc_calculer_secret(self):
        if self._cc_send_priv_val is None or self._cc_recv_pub_val is None:
            messagebox.showwarning("Attention", "Generer les cles des deux cotes d'abord !")
            return
        if self._cc_recv_priv_val is None or self._cc_send_pub_val is None:
            messagebox.showwarning("Attention", "Generer les cles des deux cotes d'abord !")
            return
        try:
            S_s = self.curve.scalar_mult(self._cc_send_priv_val, self._cc_recv_pub_val)
            S_r = self.curve.scalar_mult(self._cc_recv_priv_val, self._cc_send_pub_val)
            self._cc_sv_secret_s.set(self._cc_pub_str(S_s))
            self._cc_sv_secret_r.set(self._cc_pub_str(S_r))
        except Exception as e:
            messagebox.showerror("Erreur", str(e))

    def _cc_chiffrer_signer(self):
        if self._cc_send_priv_val is None:
            messagebox.showwarning("Attention", "Generer les cles expediteur d'abord !")
            return
        if self._cc_recv_pub_val is None:
            messagebox.showwarning("Attention", "Generer les cles destinataire d'abord !")
            return
        msg = self._cc_ent_msg.get().strip()
        if not msg:
            messagebox.showwarning("Attention", "Entrer un message !")
            return
        mode = getattr(self, "_cc_mode", "chiffrer_puis_signer")
        try:
            if mode == "chiffrer_puis_signer":
                # 1. Chiffrer le message
                C1, cipher_bytes, S = self.cipher.encrypt(msg, self._cc_recv_pub_val)
                self._cc_enc_C1    = C1
                self._cc_enc_bytes = cipher_bytes
                # 2. Signer le message chiffre (hex)
                msg_to_sign = cipher_bytes.hex()
                sig = self.ecdsa.sign(msg_to_sign, self._cc_sig_priv_val)
                self._cc_op_log = "1. CHIFFREMENT du message\n2. SIGNATURE du message chiffre"
            else:  # signer_puis_chiffrer
                # 1. Signer le message original
                sig = self.ecdsa.sign(msg, self._cc_sig_priv_val)
                # 2. Chiffrer le message original
                C1, cipher_bytes, S = self.cipher.encrypt(msg, self._cc_recv_pub_val)
                self._cc_enc_C1    = C1
                self._cc_enc_bytes = cipher_bytes
                self._cc_op_log = "1. SIGNATURE du message original\n2. CHIFFREMENT du message"
            self._cc_signature_val = sig
            r, s = sig
            self._cc_sv_sig_r.set(hex(r) if r > 9999 else str(r))
            self._cc_sv_sig_s.set(hex(s) if s > 9999 else str(s))
            self._cc_update_network()
            self._log("[CC] " + self._cc_op_log.replace("\n", " | "))
        except Exception as e:
            messagebox.showerror("Erreur chiffrement", str(e))

    def _cc_dechiffrer_verifier(self):
        if self._cc_enc_C1 is None:
            messagebox.showwarning("Attention", "L'expediteur doit d'abord chiffrer + signer !")
            return
        if self._cc_recv_priv_val is None:
            messagebox.showwarning("Attention", "Generer les cles du destinataire d'abord !")
            return
        mode = getattr(self, "_cc_mode", "chiffrer_puis_signer")
        try:
            t = self._cc_txt_resultat
            t.config(state="normal")
            t.delete("1.0", "end")

            if mode == "chiffrer_puis_signer":
                # La signature porte sur le message CHIFFRE
                # 1. Verifier la signature du chiffre d'abord
                msg_signed = self._cc_enc_bytes.hex()
                valid = self.ecdsa.verify(msg_signed, self._cc_signature_val, self._cc_sig_pub_val)
                # 2. Puis dechiffrer
                decrypted = self.cipher.decrypt(
                    self._cc_enc_C1, self._cc_enc_bytes, self._cc_recv_priv_val)
                t.insert("end", "ETAPE 1 -- Verification signature (chiffre) :\n", "accent")
                t.insert("end", "  Signature : " + ("VALIDE\n" if valid else "INVALIDE !\n"),
                         "success" if valid else "error")
                t.insert("end", "\nETAPE 2 -- Dechiffrement :\n", "accent")
                t.insert("end", "  " + decrypted + "\n", "success")
            else:
                # La signature porte sur le message ORIGINAL
                # 1. Dechiffrer d'abord
                decrypted = self.cipher.decrypt(
                    self._cc_enc_C1, self._cc_enc_bytes, self._cc_recv_priv_val)
                # 2. Verifier la signature du message original
                valid = self.ecdsa.verify(decrypted, self._cc_signature_val, self._cc_sig_pub_val)
                t.insert("end", "ETAPE 1 -- Dechiffrement :\n", "accent")
                t.insert("end", "  " + decrypted + "\n", "success")
                t.insert("end", "\nETAPE 2 -- Verification signature (original) :\n", "accent")
                t.insert("end", "  Signature : " + ("VALIDE\n" if valid else "INVALIDE !\n"),
                         "success" if valid else "error")

            rej = not self.ecdsa.verify(
                decrypted + "X", self._cc_signature_val, self._cc_sig_pub_val)
            t.insert("end", "\nIntegrite message  : ", "dim")
            t.insert("end", "GARANTIE\n" if rej else "PROBLEME\n",
                     "success" if rej else "error")
            t.insert("end", "Identite expediteur: ", "dim")
            t.insert("end", "VERIFIEE\n" if valid else "NON VERIFIEE\n",
                     "success" if valid else "error")
            t.config(state="disabled")
            self._log("[CC] Dechiffrement effectue -- mode: " + mode)
        except Exception as e:
            messagebox.showerror("Erreur dechiffrement", str(e))

    def _cc_demo_auto(self):
        try:
            self._cc_gen_sender()
            self._cc_gen_receiver()
            self._cc_calculer_secret()
            self._cc_chiffrer_signer()
            self._cc_dechiffrer_verifier()
        except Exception as e:
            messagebox.showerror("Erreur demo", str(e))

    def _cc_reset(self):
        self._cc_send_priv_val = None
        self._cc_send_pub_val  = None
        self._cc_recv_priv_val = None
        self._cc_recv_pub_val  = None
        self._cc_sig_priv_val  = None
        self._cc_sig_pub_val   = None
        self._cc_signature_val = None
        self._cc_enc_C1        = None
        self._cc_enc_bytes     = None
        for sv_var, val in [
            (self._cc_sv_send_priv, ""),
            (self._cc_sv_send_pub,  "(pas encore calcule)"),
            (self._cc_sv_recv_priv, ""),
            (self._cc_sv_recv_pub,  "(pas encore calcule)"),
            (self._cc_sv_sig_priv,  ""),
            (self._cc_sv_sig_pub,   "(pas encore calcule)"),
            (self._cc_sv_secret_s,  ""),
            (self._cc_sv_secret_r,  ""),
            (self._cc_sv_sig_r,     "--"),
            (self._cc_sv_sig_s,     "--"),
        ]:
            sv_var.set(val)
        try:
            self._net_c1.config(text="(en attente du chiffrement...)")
            self._net_hex.config(state="normal")
            self._net_hex.delete("1.0", "end")
            self._net_hex.config(state="disabled")
            self._net_sig_lbl.config(text="(en attente de la signature...)")
            self._net_q_send.config(text="Q expediteur   : (en attente)")
            self._net_q_recv.config(text="Q destinataire : (en attente)")
            self._net_q_sig.config(text="Q signature    : (en attente)")
            self._cc_txt_resultat.config(state="normal")
            self._cc_txt_resultat.delete("1.0", "end")
            self._cc_txt_resultat.config(state="disabled")
        except Exception:
            pass

    def _cc_gen_alice(self):
        self._cc_gen_sender()

    def _cc_gen_bob(self):
        self._cc_gen_receiver()

    def _cc_calc_alice_manual(self):
        self._cc_calc_sender_manual()

    def _cc_calc_bob_manual(self):
        self._cc_calc_receiver_manual()


    def _rx_gen_bob(self):
        if not self.cipher:
            messagebox.showerror("Erreur", "Aucune courbe chargee.")
            return
        try:
            d, q = self.cipher.generate_keypair()
            self._rx_bob_priv_val = d
            self._rx_bob_pub_val  = q
            self._rx_bob_priv.delete(0, "end")
            self._rx_bob_priv.insert(0, str(d))
            px = hex(q[0]) if q[0] > 9999 else str(q[0])
            py = hex(q[1]) if q[1] > 9999 else str(q[1])
            self._rx_bob_pub_lbl.config(
                text="Q Bob = (" + px + ", " + py + ")  =>  A donner a Alice")
            self._rx_export_lbl.config(text="(" + px + ", " + py + ")")
        except Exception as e:
            messagebox.showerror("Erreur", str(e))

    def _rx_calc_bob(self):
        raw = self._rx_bob_priv.get().strip()
        if not raw or not raw.isdigit():
            messagebox.showwarning("Attention", "Saisir un entier d pour Bob.")
            return
        try:
            d = int(raw)
            if d < 1 or d >= self.n:
                messagebox.showerror("Erreur", "d doit etre entre 1 et " + str(self.n-1))
                return
            q = self.curve.scalar_mult(d, self.G)
            self._rx_bob_priv_val = d
            self._rx_bob_pub_val  = q
            px = hex(q[0]) if q[0] > 9999 else str(q[0])
            py = hex(q[1]) if q[1] > 9999 else str(q[1])
            self._rx_bob_pub_lbl.config(
                text="Q Bob = (" + px + ", " + py + ")  =>  A donner a Alice")
            self._rx_export_lbl.config(text="(" + px + ", " + py + ")")
        except Exception as e:
            messagebox.showerror("Erreur", str(e))

    def _rx_dechiffrer(self):
        if not hasattr(self, "_rx_bob_priv_val") or self._rx_bob_priv_val is None:
            raw = self._rx_bob_priv.get().strip()
            if not raw or not raw.isdigit():
                messagebox.showwarning("Attention", "Entrer ou generer la cle privee de Bob.")
                return
            self._rx_bob_priv_val = int(raw)
        d_bob = self._rx_bob_priv_val
        try:
            cx = int(self._rx_c1x.get().strip())
            cy = int(self._rx_c1y.get().strip())
            C1 = (cx, cy)
        except ValueError:
            messagebox.showerror("Erreur", "C1 invalide. Entrer x et y.")
            return
        raw_hex = self._rx_hex.get("1.0", "end").strip().replace(" ", "").replace("\n", "")
        if not raw_hex:
            messagebox.showwarning("Attention", "Coller les octets chiffres (hex).")
            return
        try:
            cipher_bytes = bytes.fromhex(raw_hex)
        except ValueError:
            messagebox.showerror("Erreur", "Format hex invalide.")
            return

        # Recuperer signature et Q Alice si fournis
        rr = self._rx_sig_r.get().strip()
        rs = self._rx_sig_s.get().strip()
        qx = self._rx_qax.get().strip()
        qy = self._rx_qay.get().strip()
        has_sig = rr and rs and qx and qy
        sig_tuple = None
        Q_alice   = None
        if has_sig:
            try:
                rv   = int(rr, 16) if rr.startswith("0x") else int(rr)
                sv   = int(rs, 16) if rs.startswith("0x") else int(rs)
                qxv  = int(qx, 16) if qx.startswith("0x") else int(qx)
                qyv  = int(qy, 16) if qy.startswith("0x") else int(qy)
                sig_tuple = (rv, sv)
                Q_alice   = (qxv, qyv)
            except Exception:
                has_sig = False

        mode = getattr(self, "_cc_mode", "dechiffrer_puis_verifier")
        t = self._rx_txt_result
        t.config(state="normal")
        t.delete("1.0", "end")

        try:
            if mode == "verifier_puis_dechiffrer":
                # 1. Verifier la signature du chiffre d'abord
                t.insert("end", "ETAPE 1 -- Verification signature :\n", "accent")
                if has_sig:
                    sig_valid = self.ecdsa.verify(raw_hex, sig_tuple, Q_alice)
                    t.insert("end", "  Signature : " + ("VALIDE\n" if sig_valid else "INVALIDE !\n"),
                             "success" if sig_valid else "error")
                else:
                    t.insert("end", "  (non verifiee -- r, s, Q Alice vides)\n", "warning")
                    sig_valid = None
                # 2. Dechiffrer
                decrypted = self.cipher.decrypt(C1, cipher_bytes, d_bob)
                t.insert("end", "\nETAPE 2 -- Dechiffrement :\n", "accent")
                t.insert("end", "  " + decrypted + "\n", "success")
            else:
                # dechiffrer_puis_verifier (defaut)
                # 1. Dechiffrer
                decrypted = self.cipher.decrypt(C1, cipher_bytes, d_bob)
                t.insert("end", "ETAPE 1 -- Dechiffrement :\n", "accent")
                t.insert("end", "  " + decrypted + "\n", "success")
                # 2. Verifier la signature du message original
                t.insert("end", "\nETAPE 2 -- Verification signature :\n", "accent")
                if has_sig:
                    sig_valid = self.ecdsa.verify(decrypted, sig_tuple, Q_alice)
                    t.insert("end", "  Signature : " + ("VALIDE\n" if sig_valid else "INVALIDE !\n"),
                             "success" if sig_valid else "error")
                else:
                    t.insert("end", "  (non verifiee -- r, s, Q Alice vides)\n", "warning")
                    sig_valid = None

        except Exception as e:
            messagebox.showerror("Erreur dechiffrement", "Echec. Verifier C1 et octets.\n" + str(e))
            t.config(state="disabled")
            return

        t.config(state="disabled")

    def _rx_reset(self):
        try:
            for w in [self._rx_bob_priv, self._rx_c1x, self._rx_c1y,
                      self._rx_sig_r, self._rx_sig_s, self._rx_qax, self._rx_qay]:
                w.delete(0, "end")
            self._rx_hex.delete("1.0", "end")
            self._rx_bob_pub_lbl.config(text="Q Bob = (pas encore calcule)")
            self._rx_export_lbl.config(text="(generer les cles Bob d'abord)")
            self._rx_txt_result.config(state="normal")
            self._rx_txt_result.delete("1.0", "end")
            self._rx_txt_result.config(state="disabled")
            self._rx_bob_priv_val = None
            self._rx_bob_pub_val  = None
        except Exception:
            pass

    def _add_tags(self, widget):
        widget.tag_config("accent",  foreground=ACCENT)
        widget.tag_config("success", foreground=SUCCESS)
        widget.tag_config("error",   foreground=ERROR)
        widget.tag_config("warning", foreground=WARNING)
        widget.tag_config("dim",     foreground=TEXT2)
        widget.tag_config("bold",    font=("Courier New", 9, "bold"),
                                     foreground=TEXT)

    def _log(self, msg):
        self.txt_log.insert("end", msg + "\n")
        self.txt_log.see("end")

    # ----------------------------------------------------------
    #  FONCTIONS RESET
    # ----------------------------------------------------------

    def _reset_global(self):
        if not messagebox.askyesno("Confirmation",
            "Effacer TOUTES les donnees ?"):
            return
        self._reset_ecdh_complet()
        self._reset_chiffrement_complet()
        self._reset_ecdsa_complet()
        self._reset_ops_results()
        self._reset_ops_fields()
        self._clear_text(self.txt_info)
        self.canvas.delete("all")
        messagebox.showinfo("Reset", "Toutes les donnees effacees !")

    def _reset_ecdh_user(self, who, ent_priv, txt_pub):
        ent_priv.delete(0, "end")
        ent_priv.insert(0, "(cliquer Generer)")
        txt_pub.config(state="normal")
        txt_pub.delete("1.0", "end")
        txt_pub.config(state="disabled")
        if who == "alice":
            self.alice_priv = None
            self.alice_pub  = None
        else:
            self.bob_priv = None
            self.bob_pub  = None

    def _reset_alice(self):
        self._reset_ecdh_user("alice",
            self.ent_alice_priv, self.txt_alice_pub)

    def _reset_bob(self):
        self._reset_ecdh_user("bob",
            self.ent_bob_priv, self.txt_bob_pub)

    def _reset_ecdh_complet(self):
        self._reset_alice()
        self._reset_bob()
        self._clear_text(self.txt_ecdh)

    def _reset_chif_keys(self):
        self.chif_priv  = None
        self.chif_pub   = None
        self._enc_C1    = None
        self._enc_bytes = None
        self._clear_entry(self.ent_chif_priv, "(cliquer Generer)")
        self._clear_entry(self.ent_chif_pub,  "(cliquer Generer)")

    def _reset_chiffrement_complet(self):
        self._reset_chif_keys()
        self._clear_entry(self.ent_plain, "")
        self._clear_text(self.txt_cipher)
        self._clear_text(self.txt_decrypted)

    def _reset_ecdsa_keys(self):
        self.sig_priv  = None
        self.sig_pub   = None
        self.signature = None
        self._clear_entry(self.ent_sig_priv, "(cliquer Generer)")
        self._clear_entry(self.ent_sig_pub,  "(cliquer Generer)")

    def _reset_ecdsa_complet(self):
        self._reset_ecdsa_keys()
        self._clear_entry(self.ent_message, "")
        self._clear_text(self.txt_ecdsa)

    def _reset_add_fields(self):
        for attr in ["e_px", "e_py", "e_qx", "e_qy"]:
            getattr(self, attr).delete(0, "end")
        self.lbl_add_result.config(text="(cliquer Calculer)", fg=TEXT2)

    def _reset_mul_fields(self):
        for attr in ["e_k", "e_mpx", "e_mpy"]:
            getattr(self, attr).delete(0, "end")
        self.lbl_mul_result.config(text="(cliquer Calculer)", fg=TEXT2)

    def _reset_ops_results(self):
        self.lbl_add_result.config(text="(cliquer Calculer)", fg=TEXT2)
        self.lbl_mul_result.config(text="(cliquer Calculer)", fg=TEXT2)
        self.txt_log.delete("1.0", "end")

    def _reset_ops_fields(self):
        for attr, val in [("e_px", "3"), ("e_py", "6"),
                          ("e_qx", "39"), ("e_qy", "91")]:
            e = getattr(self, attr)
            e.delete(0, "end")
            e.insert(0, val)
        for attr, val in [("e_k", "2"), ("e_mpx", "3"), ("e_mpy", "6")]:
            e = getattr(self, attr)
            e.delete(0, "end")
            e.insert(0, val)
        self.lbl_add_result.config(text="(cliquer Calculer)", fg=TEXT2)
        self.lbl_mul_result.config(text="(cliquer Calculer)", fg=TEXT2)

    def _use_G_as_P(self):
        """Mettre les coordonnees de G dans les champs P de l addition."""
        if self.G:
            self.e_px.delete(0, "end")
            self.e_px.insert(0, str(self.G[0]))
            self.e_py.delete(0, "end")
            self.e_py.insert(0, str(self.G[1]))

    def _use_G_as_MP(self):
        """Mettre les coordonnees de G dans les champs P de la multiplication."""
        if self.G:
            self.e_mpx.delete(0, "end")
            self.e_mpx.insert(0, str(self.G[0]))
            self.e_mpy.delete(0, "end")
            self.e_mpy.insert(0, str(self.G[1]))

    # ----------------------------------------------------------
    #  CHARGEMENT COURBE
    # ----------------------------------------------------------

    def _charger_rapide(self, name):
        self.curve_var.set(name)
        self._load_curve(name)

    def _load_curve(self, name):
        try:
            cfg = CURVES[name]
            self.curve  = EllipticCurve(cfg["a"], cfg["b"], cfg["p"])
            self.G      = (cfg["Gx"], cfg["Gy"])
            self.n      = cfg["n"]
            self.ecdh   = ECDH(self.curve, self.G, self.n)
            self.ecdsa  = ECDSA(self.curve, self.G, self.n)
            self.cipher = ECCCipher(self.curve, self.G, self.n)
            self.lbl_desc.config(text=cfg["desc"])
            self.lbl_status.config(text="COURBE CHARGEE", fg=SUCCESS)
            self._refresh_info()
            self._draw_curve()
        except Exception as e:
            messagebox.showerror("Erreur", str(e))

    def _refresh_info(self):
        name = self.curve_var.get()
        cfg  = CURVES[name]
        p    = cfg["p"]
        t    = self.txt_info
        t.configure(state="normal")
        t.delete("1.0", "end")
        t.insert("end", name + "\n", "accent")
        t.insert("end", "=" * 36 + "\n\n", "dim")
        eq = "y^2 = x^3"
        if cfg["a"] != 0:
            eq += " + " + str(cfg["a"]) + "x"
        eq += " + " + str(cfg["b"]) + "  (mod p)"
        t.insert("end", "Equation : " + eq + "\n\n")
        try:
            eq2 = "y^2 = x^3"
            if cfg["a"] != 0:
                eq2 += " + " + str(cfg["a"]) + "x"
            eq2 += " + " + str(cfg["b"]) + "  (mod " + str(p) + ")"
            self.lbl_eq_active.config(text=eq2)
        except Exception:
            pass
        p_str  = hex(p)         if p         > 1000 else str(p)
        gx_str = hex(cfg["Gx"]) if cfg["Gx"] > 1000 else str(cfg["Gx"])
        gy_str = hex(cfg["Gy"]) if cfg["Gy"] > 1000 else str(cfg["Gy"])
        n_str  = hex(cfg["n"])  if cfg["n"]  > 1000 else str(cfg["n"])
        t.insert("end", "p = " + p_str + "\n")
        t.insert("end", "a = " + str(cfg["a"]) + "\n")
        t.insert("end", "b = " + str(cfg["b"]) + "\n")
        t.insert("end", "\nPoint generateur G :\n", "bold")
        t.insert("end", "  x = " + gx_str + "\n")
        t.insert("end", "  y = " + gy_str + "\n")
        t.insert("end", "\nOrdre n = " + n_str + "\n")
        t.insert("end", "\nVerifications :\n", "bold")
        on = self.curve.is_on_curve(self.G)
        t.insert("end",
                 "  G sur la courbe : " + ("OUI" if on else "NON") + "\n",
                 "success" if on else "error")
        pp = is_prime(p)
        t.insert("end",
                 "  p est premier : " + ("OUI" if pp else "NON") + "\n",
                 "success" if pp else "error")
        if p <= 500:
            pts = self.curve.get_curve_points()
            t.insert("end",
                     "\nNombre de points : " + str(len(pts)+1) + "\n")
        t.configure(state="disabled")

    # ----------------------------------------------------------
    #  VISUALISATION
    # ----------------------------------------------------------

    def _draw_curve(self):
        c = self.canvas
        c.delete("all")
        p  = self.curve.p
        W, H   = 570, 380
        margin = 50

        c.create_rectangle(0, 0, W, H, fill="#07091A", outline="")
        nb_grid = 8
        for i in range(1, nb_grid):
            xi = margin + int(i / nb_grid * (W - margin - 10))
            yi = margin + int(i / nb_grid * (H - margin - 10))
            c.create_line(xi, margin, xi, H-margin, fill="#1A1E35", dash=(2,6))
            c.create_line(margin, yi, W-10, yi, fill="#1A1E35", dash=(2,6))

        if p > 500:
            c.create_rectangle(W//2-190, H//2-65, W//2+190, H//2+65,
                                fill="#141728", outline=ACCENT2, width=2)
            c.create_text(W//2, H//2-22,
                          text="Courbe de production",
                          fill=ACCENT, font=("Courier New", 13, "bold"))
            c.create_text(W//2, H//2+8,
                          text="p trop grand pour visualisation",
                          fill=TEXT2, font=("Courier New", 9))
            c.create_text(W//2, H//2+32,
                          text="Choisir p=97 ou p=211 pour voir les points",
                          fill=WARNING, font=("Courier New", 9))
            for i in range(0, 360, 30):
                x1 = W//2 + int(80*math.cos(math.radians(i)))
                y1 = H//2 + int(80*math.sin(math.radians(i)))
                x2 = W//2 + int(100*math.cos(math.radians(i+15)))
                y2 = H//2 + int(100*math.sin(math.radians(i+15)))
                c.create_line(x1, y1, x2, y2, fill=ACCENT2, width=1)
            return

        pts = self.curve.get_curve_points()

        def to_xy(x, y):
            sx = margin + int(x / p * (W - margin - 10))
            sy = H - margin - int(y / p * (H - margin - 10))
            return sx, sy

        c.create_line(margin-5, H-margin, W-8, H-margin,
                      fill="#3A4060", width=2, arrow="last")
        c.create_line(margin, H-margin+5, margin, 8,
                      fill="#3A4060", width=2, arrow="last")
        c.create_text(W-15, H-margin+14, text="x",
                      fill=ACCENT, font=("Courier New", 11, "bold"))
        c.create_text(margin-14, 14, text="y",
                      fill=ACCENT, font=("Courier New", 11, "bold"))
        c.create_text(margin-14, H-margin+4, text="0",
                      fill=TEXT2, font=("Courier New", 8))

        for i in range(0, p+1, max(1, p//8)):
            sx, _ = to_xy(i, 0)
            c.create_line(sx, H-margin-3, sx, H-margin+3, fill="#3A4060")
            if i % max(1, p//4) == 0:
                c.create_text(sx, H-margin+12, text=str(i),
                              fill=TEXT2, font=("Courier New", 7))
        for i in range(0, p+1, max(1, p//8)):
            _, sy = to_xy(0, i)
            c.create_line(margin-3, sy, margin+3, sy, fill="#3A4060")
            if i % max(1, p//4) == 0:
                c.create_text(margin-18, sy, text=str(i),
                              fill=TEXT2, font=("Courier New", 7))

        Gx, Gy = self.G
        for (x, y) in pts:
            sx, sy = to_xy(x, y)
            if x == Gx and y == Gy:
                c.create_oval(sx-9, sy-9, sx+9, sy+9,
                              fill="", outline=ACCENT, width=1)
                c.create_oval(sx-5, sy-5, sx+5, sy+5,
                              fill=ACCENT, outline="#00FFFF", width=1)
            else:
                c.create_oval(sx-3, sy-3, sx+3, sy+3,
                              fill="#4FC3F7", outline="#29B6F6", width=1)

        sx, sy = to_xy(Gx, Gy)
        c.create_text(sx+14, sy-12,
                      text="G("+str(Gx)+","+str(Gy)+")",
                      fill=ACCENT, font=("Courier New", 8, "bold"))

        c.create_rectangle(0, H-22, W, H, fill="#0A0C1E", outline="")
        eq = "y^2=x^3"
        if self.curve.a != 0:
            eq += "+"+str(self.curve.a)+"x"
        eq += "+"+str(self.curve.b)+"  mod "+str(p)
        c.create_text(W//2, H-11,
                      text=eq + "   |   " + str(len(pts)) + " points",
                      fill=ACCENT2, font=("Courier New", 8, "bold"))
        c.create_rectangle(W-148, 5, W-4, 22, fill="#0E1020", outline=BORDER)
        c.create_text(W-76, 13,
                      text=str(len(pts))+" pts  |  p="+str(p),
                      fill=SUCCESS, font=("Courier New", 7, "bold"))

    def _animate_mult(self):
        if self.curve.p > 500:
            messagebox.showinfo("Info", "Animation pour p <= 500 seulement.")
            return
        c    = self.canvas
        G    = self.G
        p    = self.curve.p
        W, H   = 570, 380
        margin = 50
        colors = [SUCCESS, WARNING, ACCENT, ERROR,
                  "#FF6D00", "#AA00FF", "#00BCD4",
                  "#F06292", "#FFEB3B", "#76FF03"]

        def to_xy(x, y):
            sx = margin + int(x / p * (W - margin - 10))
            sy = H - margin - int(y / p * (H - margin - 10))
            return sx, sy

        def run():
            self._draw_curve()
            pt   = G
            prev = None
            for i in range(2, min(self.n, 20)):
                pt = self.curve.point_add(pt, G)
                if pt is None: break
                sx, sy = to_xy(pt[0], pt[1])
                col = colors[i % len(colors)]
                if prev:
                    px2, py2 = to_xy(prev[0], prev[1])
                    c.create_line(px2, py2, sx, sy,
                                  fill=col, width=1, dash=(3, 4))
                c.create_oval(sx-7, sy-7, sx+7, sy+7,
                              fill="", outline=col, width=1)
                c.create_oval(sx-4, sy-4, sx+4, sy+4,
                              fill=col, outline="")
                c.create_text(sx+14, sy, text=str(i)+"G",
                              fill=col, font=("Courier New", 8, "bold"))
                prev = pt
                self.update()
                time.sleep(0.5)

        threading.Thread(target=run, daemon=True).start()

    # ----------------------------------------------------------
    #  LOGIQUE ECDH
    # ----------------------------------------------------------


    def _calc_pub_from_priv_ecdh(self, who, ent_priv, txt_pub):
        """Calcule la cle publique ECDH depuis la cle privee saisie manuellement."""
        if not self.curve:
            messagebox.showerror("Erreur", "Aucune courbe chargee.")
            return
        raw = ent_priv.get().strip()
        if not raw or raw.startswith("("):
            messagebox.showwarning("Attention",
                "Entrer une cle privee d (nombre entier)\n"
                "Exemple : 3  ou  7  ou  12")
            return
        try:
            d = int(raw)
            if d < 1 or d >= self.n:
                messagebox.showerror("Erreur",
                    "d doit etre entre 1 et " + str(self.n - 1) +
                    "\n(ordre n de la courbe = " + str(self.n) + ")")
                return
            pub = self.curve.scalar_mult(d, self.G)
            px = hex(pub[0]) if pub[0] > 9999 else str(pub[0])
            py = hex(pub[1]) if pub[1] > 9999 else str(pub[1])
            txt_pub.config(state="normal")
            txt_pub.delete("1.0", "end")
            txt_pub.insert("end", "x = " + px + "\ny = " + py)
            txt_pub.config(state="disabled")
            if who == "alice":
                self.alice_priv, self.alice_pub = d, pub
            else:
                self.bob_priv, self.bob_pub = d, pub
            self._log("[ECDH] Cle " + who + " calculee manuellement : d=" +
                      str(d) + " => Q=(" + str(pub[0]) + "," + str(pub[1]) + ")")
        except ValueError:
            messagebox.showerror("Erreur",
                "Entrer un nombre entier valide.\nExemple : 3  ou  7")

    def _calc_chif_pub_from_priv(self):
        """Calcule la cle publique de chiffrement depuis la cle privee saisie."""
        if not self.curve or not self.cipher:
            messagebox.showerror("Erreur", "Aucune courbe chargee.")
            return
        raw = self.ent_chif_priv.get().strip()
        if not raw or raw.startswith("("):
            messagebox.showwarning("Attention",
                "Entrer une cle privee d dans le champ 'Cle privee (d)'\n"
                "Exemple : 3  ou  5  ou  10")
            return
        try:
            d = int(raw)
            if d < 1 or d >= self.n:
                messagebox.showerror("Erreur",
                    "d doit etre entre 1 et " + str(self.n - 1) +
                    "\n(ordre n de la courbe = " + str(self.n) + ")")
                return
            pub = self.curve.scalar_mult(d, self.G)
            self.chif_priv = d
            self.chif_pub  = pub
            self._enc_C1    = None
            self._enc_bytes = None
            px = hex(pub[0]) if pub[0] > 9999 else str(pub[0])
            py = hex(pub[1]) if pub[1] > 9999 else str(pub[1])
            self.ent_chif_priv.delete(0, "end")
            self.ent_chif_priv.insert(0, str(d))
            self.ent_chif_pub.delete(0, "end")
            self.ent_chif_pub.insert(0, "(" + px + ", " + py + ")")
            try:
                self.lbl_chif_etat.config(
                    text="  Etat : Cle d=" + str(d) + " chargee — pret a chiffrer !",
                    fg=SUCCESS)
            except Exception:
                pass
            self._log("[Chiffrement] Cle manuelle : d=" + str(d) +
                      " => Q=(" + str(pub[0]) + "," + str(pub[1]) + ")")
        except ValueError:
            messagebox.showerror("Erreur",
                "Entrer un nombre entier valide.\nExemple : 3  ou  5")

    def _calc_ecdsa_pub_from_priv(self):
        """Calcule la cle publique ECDSA depuis la cle privee saisie manuellement."""
        if not self.curve or not self.ecdsa:
            messagebox.showerror("Erreur", "Aucune courbe chargee.")
            return
        raw = self.ent_sig_priv.get().strip()
        if not raw or raw.startswith("("):
            messagebox.showwarning("Attention",
                "Entrer une cle privee d dans le champ 'Cle privee'\n"
                "Exemple : 2  ou  4  ou  8")
            return
        try:
            d = int(raw)
            if d < 1 or d >= self.n:
                messagebox.showerror("Erreur",
                    "d doit etre entre 1 et " + str(self.n - 1) +
                    "\n(ordre n de la courbe = " + str(self.n) + ")")
                return
            pub = self.curve.scalar_mult(d, self.G)
            self.sig_priv = d
            self.sig_pub  = pub
            self.signature = None
            px = hex(pub[0]) if pub[0] > 9999 else str(pub[0])
            py = hex(pub[1]) if pub[1] > 9999 else str(pub[1])
            self.ent_sig_priv.delete(0, "end")
            self.ent_sig_priv.insert(0, str(d))
            self.ent_sig_pub.delete(0, "end")
            self.ent_sig_pub.insert(0, "(" + px + ", " + py + ")")
            self._log("[ECDSA] Cle manuelle : d=" + str(d) +
                      " => Q=(" + str(pub[0]) + "," + str(pub[1]) + ")")
        except ValueError:
            messagebox.showerror("Erreur",
                "Entrer un nombre entier valide.\nExemple : 2  ou  4")

    def _gen_ecdh(self, who, ent_priv, txt_pub):
        if not self.ecdh:
            messagebox.showerror("Erreur", "Aucune courbe chargee.")
            return
        try:
            priv, pub = self.ecdh.generate_keypair()
            ent_priv.delete(0, "end")
            ent_priv.insert(0, str(priv))
            txt_pub.config(state="normal")
            txt_pub.delete("1.0", "end")
            if pub:
                px = hex(pub[0]) if pub[0] > 999 else str(pub[0])
                py = hex(pub[1]) if pub[1] > 999 else str(pub[1])
                txt_pub.insert("end", "x = " + px + "\ny = " + py)
            txt_pub.config(state="disabled")
            if who == "alice":
                self.alice_priv, self.alice_pub = priv, pub
            else:
                self.bob_priv, self.bob_pub = priv, pub
        except Exception as e:
            messagebox.showerror("Erreur", str(e))

    def _calc_ecdh_secret(self):
        if self.alice_priv is None or self.bob_priv is None:
            messagebox.showwarning("Attention",
                "Generer les cles d Alice ET de Bob d abord.")
            return
        try:
            sa = self.ecdh.shared_secret(self.alice_priv, self.bob_pub)
            sb = self.ecdh.shared_secret(self.bob_priv,   self.alice_pub)
            t  = self.txt_ecdh
            t.configure(state="normal")
            t.delete("1.0", "end")
            if sa == sb:
                t.insert("end", "SUCCES - Secrets identiques !\n\n", "success")
                if sa:
                    sx = hex(sa[0]) if sa[0] > 999 else str(sa[0])
                    t.insert("end", "Secret x = " + sx + "\n", "accent")
                    h = hashlib.sha256(str(sa).encode()).hexdigest()
                    t.insert("end", "SHA256    = " + h + "\n", "dim")
            else:
                t.insert("end", "ERREUR - Secrets differents !\n", "error")
            t.configure(state="disabled")
        except Exception as e:
            messagebox.showerror("Erreur ECDH", str(e))

    # ----------------------------------------------------------
    #  LOGIQUE CHIFFREMENT CORRIGE
    # ----------------------------------------------------------

    def _gen_chif_keys(self):
        if not self.cipher:
            messagebox.showerror("Erreur", "Aucune courbe chargee.")
            return
        try:
            priv, pub = self.cipher.generate_keypair()
            self.chif_priv = priv
            self.chif_pub  = pub
            self._enc_C1    = None
            self._enc_bytes = None
            self.ent_chif_priv.delete(0, "end")
            self.ent_chif_priv.insert(0, str(priv))
            px = hex(pub[0]) if pub[0] > 999 else str(pub[0])
            py = hex(pub[1]) if pub[1] > 999 else str(pub[1])
            self.ent_chif_pub.delete(0, "end")
            self.ent_chif_pub.insert(0, "(" + px + ", " + py + ")")
            # Mettre a jour l indicateur d etat
            try:
                self.lbl_chif_etat.config(
                    text="  Etat : Cles generees — pret a chiffrer !",
                    fg=SUCCESS)
            except Exception:
                pass
        except Exception as e:
            messagebox.showerror("Erreur", str(e))

    def _test_auto_chiffrement(self):
        """
        Test automatique complet :
        1. Genere les cles
        2. Chiffre le message
        3. Dechiffre et verifie
        Prouve que tout fonctionne en un clic.
        """
        try:
            # 1. Generer les cles
            self._gen_chif_keys()
            # 2. Mettre un message de test si vide
            if not self.ent_plain.get().strip():
                self.ent_plain.insert(0, "Test ECC 2025 !")
            # 3. Chiffrer
            self._chiffrer()
            # 4. Dechiffrer
            self._dechiffrer()
            # Verifier le resultat
            original  = self.ent_plain.get().strip()
            try:
                t = self.txt_decrypted
                t.configure(state="normal")
                content = t.get("1.0", "end").strip()
                t.configure(state="disabled")
            except Exception:
                content = ""
            if original in content:
                try:
                    self.lbl_chif_etat.config(
                        text="  TEST AUTO : SUCCES ! Le chiffrement fonctionne parfaitement.",
                        fg=SUCCESS)
                except Exception:
                    pass
                messagebox.showinfo("Test Auto",
                    "TEST REUSSI !\n\n"
                    "Message original  : " + original + "\n"
                    "Dechiffrement     : OK\n\n"
                    "Le chiffrement ECC fonctionne correctement.")
            else:
                messagebox.showerror("Test Auto",
                    "Resultat inattendu. Verifier la courbe chargee.")
        except Exception as e:
            messagebox.showerror("Erreur test auto", str(e))

    def _chiffrer(self):
        if self.chif_pub is None:
            messagebox.showwarning("Attention",
                "Etape 1 d abord : cliquer GENERER PAIRE DE CLES !")
            return
        msg = self.ent_plain.get().strip()
        if not msg:
            messagebox.showwarning("Attention",
                "Entrer un message dans le champ texte !")
            return
        try:
            C1, cipher_bytes, S = self.cipher.encrypt(msg, self.chif_pub)
            self._enc_C1    = C1
            self._enc_bytes = cipher_bytes

            t = self.txt_cipher
            t.configure(state="normal")
            t.delete("1.0", "end")
            t.insert("end", "Original  : " + msg + "\n", "dim")
            t.insert("end", "C1        : (" +
                     str(C1[0]) + ", " + str(C1[1]) + ")\n", "dim")
            t.insert("end", "Chiffre   : " + cipher_bytes.hex() + "\n",
                     "warning")
            t.insert("end", str(len(msg)) + " caractere(s) chiffre(s)\n",
                     "accent")
            t.configure(state="disabled")
            try:
                self.lbl_chif_etat.config(
                    text="  Etat : Message chiffre — cliquer DECHIFFRER pour verifier.",
                    fg=WARNING)
            except Exception:
                pass
        except Exception as e:
            messagebox.showerror("Erreur chiffrement", str(e))

    def _dechiffrer(self):
        if self._enc_C1 is None or self._enc_bytes is None:
            messagebox.showwarning("Attention",
                "Etape 2 d abord : cliquer CHIFFRER LE MESSAGE !")
            return
        if self.chif_priv is None:
            messagebox.showwarning("Attention",
                "Cle privee manquante — regenerer les cles (Etape 1).")
            return
        try:
            decrypted = self.cipher.decrypt(
                self._enc_C1, self._enc_bytes, self.chif_priv)
            original  = self.ent_plain.get().strip()

            t = self.txt_decrypted
            t.configure(state="normal")
            t.delete("1.0", "end")
            t.insert("end", decrypted + "\n\n", "success")

            if decrypted == original:
                t.insert("end",
                    "SUCCES : message identique a l original !\n",
                    "success")
                try:
                    self.lbl_chif_etat.config(
                        text="  Etat : SUCCES — Chiffrement et dechiffrement OK !",
                        fg=SUCCESS)
                except Exception:
                    pass
            else:
                t.insert("end",
                    "ATTENTION : message different !\n",
                    "error")
                try:
                    self.lbl_chif_etat.config(
                        text="  Etat : ERREUR — Verifier la courbe et les cles.",
                        fg=ERROR)
                except Exception:
                    pass
            t.configure(state="disabled")
        except Exception as e:
            messagebox.showerror("Erreur dechiffrement", str(e))

    # ----------------------------------------------------------
    #  LOGIQUE ECDSA
    # ----------------------------------------------------------

    def _gen_ecdsa_keys(self):
        if not self.ecdsa:
            messagebox.showerror("Erreur", "Aucune courbe chargee.")
            return
        try:
            priv, pub = self.ecdsa.generate_keypair()
            self.sig_priv = priv
            self.sig_pub  = pub
            self.ent_sig_priv.delete(0, "end")
            self.ent_sig_priv.insert(0, str(priv))
            px = hex(pub[0]) if pub[0] > 999 else str(pub[0])
            py = hex(pub[1]) if pub[1] > 999 else str(pub[1])
            self.ent_sig_pub.delete(0, "end")
            self.ent_sig_pub.insert(0, "(" + px + ", " + py + ")")
        except Exception as e:
            messagebox.showerror("Erreur", str(e))

    def _ecdsa_gen_bob(self):
        """Genere les cles de Bob pour l'onglet ECDSA."""
        if not self.cipher:
            messagebox.showerror("Erreur", "Aucune courbe chargee.")
            return
        try:
            d, q = self.cipher.generate_keypair()
            self._ecdsa_bob_priv_val = d
            self._ecdsa_bob_pub_val  = q
            px = hex(q[0]) if q[0] > 9999 else str(q[0])
            py = hex(q[1]) if q[1] > 9999 else str(q[1])
            self._ecdsa_bob_priv_ent.delete(0, "end")
            self._ecdsa_bob_priv_ent.insert(0, str(d))
            self._ecdsa_bob_pub_ent.delete(0, "end")
            self._ecdsa_bob_pub_ent.insert(0, "(" + px + ", " + py + ")")
        except Exception as e:
            messagebox.showerror("Erreur", str(e))

    def _ecdsa_calc_bob(self):
        """Calcule la cle publique de Bob depuis d saisi."""
        if not self.curve:
            messagebox.showerror("Erreur", "Aucune courbe chargee.")
            return
        raw = self._ecdsa_bob_priv_ent.get().strip()
        if not raw or not raw.isdigit():
            messagebox.showwarning("Attention", "Saisir un entier d pour Bob.")
            return
        try:
            d = int(raw)
            if d < 1 or d >= self.n:
                messagebox.showerror("Erreur", "d doit etre entre 1 et " + str(self.n - 1))
                return
            q = self.curve.scalar_mult(d, self.G)
            self._ecdsa_bob_priv_val = d
            self._ecdsa_bob_pub_val  = q
            px = hex(q[0]) if q[0] > 9999 else str(q[0])
            py = hex(q[1]) if q[1] > 9999 else str(q[1])
            self._ecdsa_bob_pub_ent.delete(0, "end")
            self._ecdsa_bob_pub_ent.insert(0, "(" + px + ", " + py + ")")
        except Exception as e:
            messagebox.showerror("Erreur", str(e))

    def _signer(self):
        """Alice chiffre le message avec la cle publique de Bob ET signe avec sa cle privee."""
        if self.sig_priv is None:
            messagebox.showwarning("Attention",
                "Generer les cles d'Alice d'abord.")
            return
        if self._ecdsa_bob_pub_val is None:
            messagebox.showwarning("Attention",
                "Generer les cles de Bob d'abord.")
            return
        msg = self.ent_message.get().strip()
        if not msg:
            messagebox.showwarning("Attention", "Entrer un message.")
            return
        try:
            # 1. Chiffrer avec la cle publique de Bob
            C1, cipher_bytes, _ = self.cipher.encrypt(msg, self._ecdsa_bob_pub_val)
            self._ecdsa_enc_C1    = C1
            self._ecdsa_enc_bytes = cipher_bytes
            # 2. Signer le message original
            sig = self.ecdsa.sign(msg, self.sig_priv)
            self.signature = sig
            rs = hex(sig[0]) if sig[0] > 999 else str(sig[0])
            ss = hex(sig[1]) if sig[1] > 999 else str(sig[1])
            # 3. Mettre a jour labels Alice
            self._sig_lbl_r.config(text="r = " + rs)
            self._sig_lbl_s.config(text="s = " + ss)
            # 4. Mettre a jour le reseau public
            try:
                pub = self.sig_pub
                px = hex(pub[0]) if pub[0] > 9999 else str(pub[0])
                py = hex(pub[1]) if pub[1] > 9999 else str(pub[1])
                self._ecdsa_net_qalice.config(
                    text="(" + px + ", " + py + ")")
                cx = hex(C1[0]) if C1[0] > 9999 else str(C1[0])
                cy = hex(C1[1]) if C1[1] > 9999 else str(C1[1])
                self._ecdsa_net_c1.config(text="(" + cx + ", " + cy + ")")
                h = cipher_bytes.hex()
                self._ecdsa_net_hex.config(state="normal")
                self._ecdsa_net_hex.delete("1.0", "end")
                self._ecdsa_net_hex.insert("end",
                    " ".join(h[i:i+2] for i in range(0, len(h), 2)))
                self._ecdsa_net_hex.config(state="disabled")
                self._ecdsa_net_sig.config(
                    text="r = " + rs + "\ns = " + ss)
            except Exception:
                pass
            # 5. Informer Bob
            t = self.txt_ecdsa
            t.configure(state="normal")
            t.delete("1.0", "end")
            t.insert("end", "Message chiffre + signe.\n", "accent")
            t.insert("end", "Cliquer DECHIFFRER + VERIFIER\n", "dim")
            t.configure(state="disabled")
        except Exception as e:
            messagebox.showerror("Erreur", str(e))

    def _verifier(self):
        """Bob dechiffre avec sa cle privee et verifie la signature d'Alice."""
        if self._ecdsa_enc_C1 is None:
            messagebox.showwarning("Attention",
                "Alice doit d'abord chiffrer + signer.")
            return
        if self._ecdsa_bob_priv_val is None:
            messagebox.showwarning("Attention",
                "Generer les cles de Bob d'abord.")
            return
        try:
            # 1. Bob dechiffre avec sa cle privee
            decrypted = self.cipher.decrypt(
                self._ecdsa_enc_C1, self._ecdsa_enc_bytes,
                self._ecdsa_bob_priv_val)
            # 2. Bob verifie la signature avec la cle PUBLIQUE d'Alice
            valid = self.ecdsa.verify(decrypted, self.signature, self.sig_pub)
            tampered = decrypted + "X"
            rej = not self.ecdsa.verify(tampered, self.signature, self.sig_pub)
            t = self.txt_ecdsa
            t.configure(state="normal")
            t.delete("1.0", "end")
            t.insert("end", "MESSAGE DECHIFFRE PAR BOB\n", "accent")
            t.insert("end", "-" * 34 + "\n", "dim")
            t.insert("end", decrypted + "\n\n", "success")
            t.insert("end", "Dechiffrement      : ", "dim")
            t.insert("end", "OK\n", "success")
            t.insert("end", "Signature Alice    : ", "dim")
            t.insert("end",
                "VALIDE -- C'est bien Alice !\n" if valid else "INVALIDE !\n",
                "success" if valid else "error")
            t.insert("end", "Integrite message  : ", "dim")
            t.insert("end",
                "GARANTIE\n" if rej else "PROBLEME !\n",
                "success" if rej else "error")
            t.configure(state="disabled")
        except Exception as e:
            messagebox.showerror("Erreur dechiffrement/verification", str(e))

    # ----------------------------------------------------------
    #  OPERATIONS MANUELLES
    # ----------------------------------------------------------

    def _get_valid_point_hint(self, x_try):
        """Retourne un message d'aide avec des points valides proches."""
        if self.curve is None or self.curve.p > 500:
            return "Utiliser 'Voir points valides' pour la liste."
        pts = self.curve.get_curve_points()
        if not pts:
            return "Aucun point trouve."
        # Trouver un point avec x proche
        candidates = [p for p in pts if abs(p[0] - x_try) <= 5]
        if not candidates:
            candidates = pts[:4]
        c = candidates[:2]
        return "Essayer : " + "  ou  ".join(
            "(" + str(p[0]) + ", " + str(p[1]) + ")" for p in c)

    def _show_valid_points(self):
        """Affiche une fenetre avec les points valides de la courbe courante."""
        if self.curve is None:
            messagebox.showinfo("Info", "Charger une courbe d'abord.")
            return
        if self.curve.p > 500:
            messagebox.showinfo("Points valides",
                "La courbe a p > 500.\nTrop de points pour les afficher.\n"
                "Utiliser le bouton 'Utiliser G comme P'\n"
                "ou entrer G = (" + str(self.G[0]) + ", " + str(self.G[1]) + ")")
            return
        pts = self.curve.get_curve_points()
        win = tk.Toplevel(self)
        win.title("Points valides sur la courbe")
        win.configure(bg=BG2)
        win.geometry("520x480")
        # Titre
        tk.Label(win,
                 text="Points valides  y^2 = x^3 + " +
                      str(self.curve.a) + "x + " +
                      str(self.curve.b) + "  (mod " + str(self.curve.p) + ")",
                 bg=BG2, fg=ACCENT,
                 font=("Courier New", 10, "bold")).pack(pady=(12, 4), padx=10)
        tk.Label(win,
                 text=str(len(pts)) + " points   (cliquer un point pour l'utiliser dans P ou Q)",
                 bg=BG2, fg=TEXT2,
                 font=("Courier New", 9)).pack(pady=(0, 6))
        # Liste scrollable
        frame_list = tk.Frame(win, bg=BG2)
        frame_list.pack(fill="both", expand=True, padx=10, pady=(0, 8))
        sb = tk.Scrollbar(frame_list)
        sb.pack(side="right", fill="y")
        lb = tk.Listbox(frame_list, bg=BG3, fg=SUCCESS,
                        font=("Courier New", 10),
                        selectbackground=ACCENT2,
                        yscrollcommand=sb.set,
                        relief="flat", bd=0)
        lb.pack(side="left", fill="both", expand=True)
        sb.config(command=lb.yview)
        for pt in sorted(pts):
            lb.insert("end", "  (" + str(pt[0]) + ",  " + str(pt[1]) + ")")
        # Boutons
        btn_f = tk.Frame(win, bg=BG2)
        btn_f.pack(pady=6)
        def use_as_P():
            sel = lb.curselection()
            if sel:
                pt = sorted(pts)[sel[0]]
                self.e_px.delete(0, "end"); self.e_px.insert(0, str(pt[0]))
                self.e_py.delete(0, "end"); self.e_py.insert(0, str(pt[1]))
                win.destroy()
        def use_as_Q():
            sel = lb.curselection()
            if sel:
                pt = sorted(pts)[sel[0]]
                self.e_qx.delete(0, "end"); self.e_qx.insert(0, str(pt[0]))
                self.e_qy.delete(0, "end"); self.e_qy.insert(0, str(pt[1]))
                win.destroy()
        def use_as_MP():
            sel = lb.curselection()
            if sel:
                pt = sorted(pts)[sel[0]]
                self.e_mpx.delete(0, "end"); self.e_mpx.insert(0, str(pt[0]))
                self.e_mpy.delete(0, "end"); self.e_mpy.insert(0, str(pt[1]))
                win.destroy()
        ttk.Button(btn_f, text="Utiliser comme P (addition)",
                   command=use_as_P,
                   style="Green.TButton").pack(side="left", padx=4)
        ttk.Button(btn_f, text="Utiliser comme Q (addition)",
                   command=use_as_Q).pack(side="left", padx=4)
        ttk.Button(btn_f, text="Utiliser comme P (multiplication)",
                   command=use_as_MP,
                   style="Orange.TButton").pack(side="left", padx=4)
        tk.Label(win,
                 text="G = (" + str(self.G[0]) + ", " + str(self.G[1]) + ")  |  n = " + str(self.n),
                 bg=BG2, fg=TEXT2,
                 font=("Courier New", 9, "italic")).pack(pady=(0, 8))

    def _do_add(self):
        try:
            px_val = self.e_px.get().strip()
            py_val = self.e_py.get().strip()
            qx_val = self.e_qx.get().strip()
            qy_val = self.e_qy.get().strip()

            if not all([px_val, py_val, qx_val, qy_val]):
                self.lbl_add_result.config(
                    text="Remplir tous les champs x et y !", fg=WARNING)
                return

            P = (int(px_val), int(py_val))
            Q = (int(qx_val), int(qy_val))
            p = self.curve.p

            if not self.curve.is_on_curve(P):
                hint = self._get_valid_point_hint(P[0])
                self.lbl_add_result.config(
                    text="ERREUR : P(" + str(P[0]) + "," + str(P[1]) +
                         ") n'est pas sur la courbe !\n" + hint,
                    fg=ERROR, wraplength=300)
                self._log("[ERREUR] P" + str(P) + " pas sur la courbe. " + hint)
                return
            if not self.curve.is_on_curve(Q):
                hint = self._get_valid_point_hint(Q[0])
                self.lbl_add_result.config(
                    text="ERREUR : Q(" + str(Q[0]) + "," + str(Q[1]) +
                         ") n'est pas sur la courbe !\n" + hint,
                    fg=ERROR, wraplength=300)
                self._log("[ERREUR] Q" + str(Q) + " pas sur la courbe. " + hint)
                return

            # Calcul detaille
            x1, y1 = P
            x2, y2 = Q
            detail = "[Addition] P(" + str(x1) + "," + str(y1) + ")"
            detail += " + Q(" + str(x2) + "," + str(y2) + ")\n"

            if x1 == x2 and y1 == y2:
                # Doublement
                num = (3 * x1*x1 + self.curve.a) % p
                den = (2 * y1) % p
                lam = num * mod_inverse(den, p) % p
                detail += "  Doublement (P=Q): lambda=(" + str(3*x1*x1+self.curve.a) + \
                          "*inv(" + str(2*y1) + ")) mod " + str(p) + " = " + str(lam) + "\n"
            elif x1 == x2:
                self.lbl_add_result.config(
                    text="P + Q = Point a l infini (P et -P s annulent)", fg=WARNING)
                self._log("[Addition] P+Q = Infini (x egaux, y opposes)")
                return
            else:
                num = (y2 - y1) % p
                den = (x2 - x1) % p
                lam = num * mod_inverse(den, p) % p
                detail += "  lambda = (" + str(y2) + "-" + str(y1) + ") * inv(" + \
                          str(x2) + "-" + str(x1) + ") mod " + str(p) + " = " + str(lam) + "\n"

            R = self.curve.point_add(P, Q)
            if R is None:
                self.lbl_add_result.config(
                    text="P + Q = Point a l infini (O)", fg=WARNING)
            else:
                detail += "  x3 = " + str(lam) + "^2 - " + str(x1) + \
                          " - " + str(x2) + " mod " + str(p) + " = " + str(R[0]) + "\n"
                detail += "  y3 = " + str(lam) + "*(" + str(x1) + "-" + \
                          str(R[0]) + ") - " + str(y1) + " mod " + str(p) + " = " + str(R[1]) + "\n"
                detail += "  => R = (" + str(R[0]) + " , " + str(R[1]) + ")"
                res = "P + Q  =  ( " + str(R[0]) + " ,  " + str(R[1]) + " )"
                self.lbl_add_result.config(text=res, fg=SUCCESS)

            self._log(detail)
        except ValueError:
            self.lbl_add_result.config(
                text="ERREUR : Entrer des nombres entiers valides !",
                fg=ERROR)
        except Exception as e:
            self.lbl_add_result.config(text="Erreur : " + str(e), fg=ERROR)

    def _do_mult(self):
        try:
            k_val   = self.e_k.get().strip()
            mpx_val = self.e_mpx.get().strip()
            mpy_val = self.e_mpy.get().strip()

            if not all([k_val, mpx_val, mpy_val]):
                self.lbl_mul_result.config(
                    text="Remplir k, x et y !", fg=WARNING)
                return

            k = int(k_val)
            P = (int(mpx_val), int(mpy_val))

            if k <= 0:
                self.lbl_mul_result.config(
                    text="ERREUR : k doit etre >= 1 !", fg=ERROR)
                return
            if k > 10000:
                self.lbl_mul_result.config(
                    text="ERREUR : k trop grand (max 10000) !", fg=ERROR)
                return

            if not self.curve.is_on_curve(P):
                self.lbl_mul_result.config(
                    text="ERREUR : P(" + str(P[0]) + "," + str(P[1]) +
                         ") n est pas sur la courbe !",
                    fg=ERROR)
                return

            R = self.curve.scalar_mult(k, P)

            # Journal detaille
            detail = "[Multiplication]  " + str(k) + " * P(" + \
                     str(P[0]) + "," + str(P[1]) + ")\n"
            detail += "  = P + P + P + ... (" + str(k) + " fois)\n"
            if k <= 8:
                pt = P
                for i in range(2, k + 1):
                    pt = self.curve.point_add(pt, P)
                    if pt is None:
                        detail += "  " + str(i) + "P = Infini\n"
                        break
                    detail += "  " + str(i) + "P = (" + \
                              str(pt[0]) + "," + str(pt[1]) + ")\n"
            else:
                detail += "  (trop de pas a afficher — algorithme double-and-add)\n"

            if R is None:
                res = str(k) + " * P  =  Point a l infini (O)"
                self.lbl_mul_result.config(text=res, fg=WARNING)
                detail += "  => " + str(k) + "P = Infini"
            else:
                res = str(k) + " * P  =  ( " + str(R[0]) + " ,  " + str(R[1]) + " )"
                self.lbl_mul_result.config(text=res, fg=SUCCESS)
                detail += "  => " + str(k) + "P = (" + str(R[0]) + "," + str(R[1]) + ")"

            self._log(detail)
        except ValueError:
            self.lbl_mul_result.config(
                text="ERREUR : Entrer des nombres entiers valides !",
                fg=ERROR)
        except Exception as e:
            self.lbl_mul_result.config(text="Erreur : " + str(e), fg=ERROR)


# -------------------------------------------------------------
#  POINT D ENTREE
# -------------------------------------------------------------

if __name__ == "__main__":
    app = ECCApp()
    app.mainloop()
