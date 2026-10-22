# -*- coding: utf-8 -*-
"""Đồ án đề tài 6: Quản lý thông tin khách hàng ngân hàng (bản web Streamlit).
Lớp L06 - Nhóm 08. Phần cấu trúc dữ liệu/giải thuật giống hệt notebook Colab,
phần dưới cùng là giao diện.

Cách chạy:
    pip install streamlit pandas matplotlib
    streamlit run app.py
"""
import io
import time
import statistics
import tracemalloc

# ============================================================================
# PHẦN 1: CẤU TRÚC DỮ LIỆU VÀ GIẢI THUẬT (copy từ notebook)
# ============================================================================

import csv
import heapq
import random
import re
import unicodedata
from datetime import date, timedelta

def bo_dau(s):
    """Bỏ dấu tiếng Việt, chuyển về chữ thường. Vd: 'Nguyễn Văn Ân' -> 'nguyen van an'"""
    s = s.replace("đ", "d").replace("Đ", "D")   # đ không tách được bằng NFD nên đổi tay
    s = unicodedata.normalize("NFD", s)
    s = "".join(c for c in s if unicodedata.category(c) != "Mn")
    return " ".join(s.lower().split())

EMAIL_RE = re.compile(r"^[\w.+-]+@[\w-]+(\.[\w-]+)+$")
LOAI_HOP_LE = {"Thường", "VIP", "Doanh nghiệp"}
NGUONG_VIP = 1000000000      # số dư từ 1 tỷ trở lên được xếp vào diện ưu tiên

def doi_bool(x):
    """Đổi giá trị đọc từ form/CSV (True, 'True', '1', 'có'...) sang bool. Không hiểu thì trả về None."""
    if isinstance(x, bool):
        return x
    x = str(x).strip().lower()
    if x in ("true", "1", "có", "co", "x"):
        return True
    if x in ("false", "0", "không", "khong"):
        return False
    return None


class TrieNode:
    def __init__(self):
        self.con = {}        # ký tự -> nút con
        self.ds_ma = set()   # các mã KH có đường đi qua nút này


class Trie:
    """Cây tiền tố, dùng để tìm các mã KH có họ tên bắt đầu bằng 1 tiền tố. Độ phức tạp O(L)."""
    def __init__(self):
        self.goc = TrieNode()

    def chen(self, khoa, ma_kh):
        nut = self.goc
        for ch in khoa:
            nut = nut.con.setdefault(ch, TrieNode())
            nut.ds_ma.add(ma_kh)

    def xoa(self, khoa, ma_kh):
        nut = self.goc
        for ch in khoa:
            if ch not in nut.con:
                return
            nut = nut.con[ch]
            nut.ds_ma.discard(ma_kh)

    def tim_tien_to(self, tien_to):
        nut = self.goc
        for ch in tien_to:
            if ch not in nut.con:
                return set()
            nut = nut.con[ch]
        return set(nut.ds_ma)


def sap_xep_tron(ds, key, reverse=False):
    """Merge Sort tự cài, ổn định, O(n log n). Trả về danh sách mới, không sửa ds."""
    if len(ds) <= 1:
        return list(ds)
    giua = len(ds) // 2
    trai = sap_xep_tron(ds[:giua], key, reverse)
    phai = sap_xep_tron(ds[giua:], key, reverse)
    kq = []
    i = j = 0
    while i < len(trai) and j < len(phai):
        a, b = key(trai[i]), key(phai[j])
        lay_trai = (a >= b) if reverse else (a <= b)   # có dấu = để giữ thứ tự của các phần tử bằng nhau
        if lay_trai:
            kq.append(trai[i])
            i += 1
        else:
            kq.append(phai[j])
            j += 1
    kq.extend(trai[i:])
    kq.extend(phai[j:])
    return kq


def sap_xep_chen(ds, key, reverse=False):
    """Insertion Sort O(n^2), chỉ để so sánh tốc độ với Merge Sort."""
    a = list(ds)
    for i in range(1, len(a)):
        x = a[i]
        kx = key(x)
        j = i - 1
        while j >= 0 and ((key(a[j]) < kx) if reverse else (key(a[j]) > kx)):
            a[j + 1] = a[j]
            j -= 1
        a[j + 1] = x
    return a


def tim_tuan_tu(ds, ma_kh):
    """Linear Search, O(n)."""
    for kh in ds:
        if kh["ma_kh"] == ma_kh:
            return kh
    return None


def tim_nhi_phan(ds_da_sap, ma_kh):
    """Binary Search, O(log n). Danh sách phải được sắp tăng dần theo ma_kh."""
    trai, phai = 0, len(ds_da_sap) - 1
    while trai <= phai:
        giua = (trai + phai) // 2
        ma_giua = ds_da_sap[giua]["ma_kh"]
        if ma_giua == ma_kh:
            return ds_da_sap[giua]
        elif ma_giua < ma_kh:
            trai = giua + 1
        else:
            phai = giua - 1
    return None


def trung_hai_vong_lap(ds):
    """Tìm CCCD trùng bằng 2 vòng for lồng nhau, O(n^2)."""
    trung = []
    for i in range(len(ds)):
        for j in range(i + 1, len(ds)):
            if ds[i]["cccd"] == ds[j]["cccd"]:
                trung.append((ds[i]["ma_kh"], ds[j]["ma_kh"]))
    return trung


def trung_bang_set(ds):
    """Tìm CCCD trùng bằng dict/set, O(n)."""
    da_thay = {}
    trung = []
    for kh in ds:
        if kh["cccd"] in da_thay:
            trung.append((da_thay[kh["cccd"]], kh["ma_kh"]))
        else:
            da_thay[kh["cccd"]] = kh["ma_kh"]
    return trung


class QuanLyKhachHang:
    TRUONG = ["ma_kh", "ho_ten", "cccd", "sdt", "email", "dia_phuong", "loai_kh", "so_du", "ngay_dk",
              "diem_tin_dung", "is_vip"]

    def __init__(self):
        self.ds = []                # list: mọi hồ sơ theo thứ tự nhập
        self.chi_muc = {}           # dict: ma_kh -> hồ sơ, tra cứu O(1)
        self.tap_cccd = set()       # set: kiểm tra trùng CCCD
        self.tap_sdt = set()        # set: kiểm tra trùng SĐT
        self.tap_email = set()      # set: kiểm tra trùng email
        self.trie = Trie()          # trie: gợi ý theo tiền tố họ tên
        self.ngan_xep = []          # stack: lịch sử thao tác để hoàn tác
        self._heap_vip = []         # heap hàng đợi VIP (heapq là min-heap nên đảo dấu số dư và điểm tín dụng)
        self.da_phuc_vu = set()     # mã khách đã được phục vụ, không đưa lại vào hàng đợi
        self._can_dung_lai = False  # True khi vừa sửa/xóa hồ sơ, cần dựng lại heap trước khi dùng

    def __len__(self):
        return len(self.ds)

    @staticmethod
    def chuan_hoa(rec):
        r = dict(rec)
        r["ma_kh"] = str(r.get("ma_kh", "")).strip().upper()
        r["ho_ten"] = " ".join(str(r.get("ho_ten", "")).split())
        r["cccd"] = str(r.get("cccd", "")).strip()
        r["sdt"] = str(r.get("sdt", "")).strip()
        r["email"] = str(r.get("email", "")).strip().lower()
        r["dia_phuong"] = str(r.get("dia_phuong", "")).strip()
        r["loai_kh"] = str(r.get("loai_kh", "")).strip()
        try:
            r["so_du"] = float(r.get("so_du"))
        except (TypeError, ValueError):
            r["so_du"] = None
        try:
            r["diem_tin_dung"] = int(str(r.get("diem_tin_dung")).strip())
        except ValueError:
            r["diem_tin_dung"] = None
        r["is_vip"] = doi_bool(r.get("is_vip"))
        return r

    def kiem_tra_hop_le(self, r):
        for tr in self.TRUONG:
            if tr not in r or r[tr] is None or r[tr] == "":
                return False, "Thiếu trường '" + tr + "'"
        if not (len(r["cccd"]) == 12 and r["cccd"].isdigit()):
            return False, "CCCD phải gồm 12 chữ số"
        if not (len(r["sdt"]) == 10 and r["sdt"].isdigit() and r["sdt"].startswith("0")):
            return False, "SĐT phải gồm 10 chữ số, bắt đầu bằng 0"
        if not EMAIL_RE.match(r["email"]):
            return False, "Email không đúng định dạng"
        if r["loai_kh"] not in LOAI_HOP_LE:
            return False, "Loại khách hàng không hợp lệ"
        if r["so_du"] < 0:
            return False, "Số dư âm"
        if not (150 <= r["diem_tin_dung"] <= 750):
            return False, "Điểm tín dụng phải nằm trong khoảng 150-750"
        return True, ""

    def _kiem_tra_trung(self, r, bo_qua_ma=None):
        # bo_qua_ma dùng khi sửa: giữ nguyên CCCD/SĐT/email của chính hồ sơ đó thì không tính là trùng
        if r["ma_kh"] in self.chi_muc and r["ma_kh"] != bo_qua_ma:
            return "Trùng mã khách hàng"
        cu = self.chi_muc.get(bo_qua_ma) if bo_qua_ma else None
        if r["cccd"] in self.tap_cccd and not (cu and cu["cccd"] == r["cccd"]):
            return "Trùng CCCD"
        if r["sdt"] in self.tap_sdt and not (cu and cu["sdt"] == r["sdt"]):
            return "Trùng số điện thoại"
        if r["email"] in self.tap_email and not (cu and cu["email"] == r["email"]):
            return "Trùng email"
        return ""

    def _chi_muc_hoa(self, r):
        self.chi_muc[r["ma_kh"]] = r
        self.tap_cccd.add(r["cccd"])
        self.tap_sdt.add(r["sdt"])
        self.tap_email.add(r["email"])
        tu = bo_dau(r["ho_ten"]).split()
        for i in range(len(tu)):                 # chèn mọi hậu tố của họ tên để tìm được cả theo tên gọi
            self.trie.chen(" ".join(tu[i:]), r["ma_kh"])
        self._vao_hang_doi_vip(r)

    def _go_chi_muc(self, r):
        self.chi_muc.pop(r["ma_kh"], None)
        self.tap_cccd.discard(r["cccd"])
        self.tap_sdt.discard(r["sdt"])
        self.tap_email.discard(r["email"])
        tu = bo_dau(r["ho_ten"]).split()
        for i in range(len(tu)):
            self.trie.xoa(" ".join(tu[i:]), r["ma_kh"])
        self.da_phuc_vu.discard(r["ma_kh"])
        self._can_dung_lai = True                  # lần dùng hàng đợi tới sẽ dựng lại heap

    # ---------- hàng đợi ưu tiên VIP ----------
    @staticmethod
    def la_vip(r):
        """Thuộc diện ưu tiên nếu được đánh dấu VIP hoặc số dư từ 1 tỷ trở lên."""
        return r["is_vip"] or r["so_du"] >= NGUONG_VIP

    def _vao_hang_doi_vip(self, r):
        if self.la_vip(r):
            heapq.heappush(self._heap_vip, (-r["so_du"], -r["diem_tin_dung"], r["ma_kh"]))   # O(log n)

    def _cap_nhat_hang_doi(self):
        # sau khi sửa hoặc xóa thì dựng lại heap từ dữ liệu hiện tại, O(n)
        if self._can_dung_lai:
            self._heap_vip = [(-r["so_du"], -r["diem_tin_dung"], r["ma_kh"])
                              for r in self.chi_muc.values()
                              if self.la_vip(r) and r["ma_kh"] not in self.da_phuc_vu]
            heapq.heapify(self._heap_vip)
            self._can_dung_lai = False

    def so_luong_vip(self):
        self._cap_nhat_hang_doi()
        return len(self._heap_vip)

    def phuc_vu_vip(self):
        # lấy khách ưu tiên nhất ra khỏi hàng đợi, O(log n); hết khách thì trả về None
        # hồ sơ vẫn còn trong danh sách, chỉ không còn đứng trong hàng đợi
        self._cap_nhat_hang_doi()
        if not self._heap_vip:
            return None
        ma_kh = heapq.heappop(self._heap_vip)[2]
        self.da_phuc_vu.add(ma_kh)
        return self.chi_muc[ma_kh]

    def xem_hang_doi_vip(self, k=10):
        # xem k khách đầu hàng đợi mà không lấy họ ra
        self._cap_nhat_hang_doi()
        return [self.chi_muc[m[2]] for m in heapq.nsmallest(k, self._heap_vip)]

    def them(self, rec, ghi_undo=True):
        r = self.chuan_hoa(rec)
        ok, ly_do = self.kiem_tra_hop_le(r)
        if not ok:
            return False, ly_do
        ly_do = self._kiem_tra_trung(r)
        if ly_do:
            return False, ly_do
        self.ds.append(r)
        self._chi_muc_hoa(r)
        if ghi_undo:
            self.ngan_xep.append(("them", r["ma_kh"]))
        return True, "Đã thêm khách hàng " + r["ma_kh"]

    def tra_cuu(self, ma_kh):
        return self.chi_muc.get(str(ma_kh).strip().upper())

    def tim_theo_ten(self, tien_to):
        tien_to = bo_dau(str(tien_to))
        if not tien_to:
            return []
        tap_ma = self.trie.tim_tien_to(tien_to)
        return [self.chi_muc[m] for m in sorted(tap_ma) if m in self.chi_muc]

    def loc(self, dia_phuong=None, loai_kh=None, so_du_tu=None, so_du_den=None):
        kq = []
        for kh in self.ds:
            if dia_phuong and kh["dia_phuong"] != dia_phuong:
                continue
            if loai_kh and kh["loai_kh"] != loai_kh:
                continue
            if so_du_tu is not None and kh["so_du"] < so_du_tu:
                continue
            if so_du_den is not None and kh["so_du"] > so_du_den:
                continue
            kq.append(kh)
        return kq

    def sua(self, ma_kh, **thay_doi):
        ma_kh = str(ma_kh).strip().upper()
        cu = self.chi_muc.get(ma_kh)
        if cu is None:
            return False, "Không tìm thấy khách hàng"
        thay_doi.pop("ma_kh", None)              # không cho đổi mã (khóa chính)
        moi = self.chuan_hoa({**cu, **thay_doi})
        ok, ly_do = self.kiem_tra_hop_le(moi)
        if not ok:
            return False, ly_do
        ly_do = self._kiem_tra_trung(moi, bo_qua_ma=ma_kh)
        if ly_do:
            return False, ly_do
        vi_tri = self.ds.index(cu)
        self._go_chi_muc(cu)
        self.ds[vi_tri] = moi
        self._chi_muc_hoa(moi)
        self.ngan_xep.append(("sua", dict(cu)))
        return True, "Đã cập nhật " + ma_kh

    def xoa(self, ma_kh, ghi_undo=True):
        ma_kh = str(ma_kh).strip().upper()
        cu = self.chi_muc.get(ma_kh)
        if cu is None:
            return False, "Không tìm thấy khách hàng"
        vi_tri = self.ds.index(cu)
        del self.ds[vi_tri]
        self._go_chi_muc(cu)
        if ghi_undo:
            self.ngan_xep.append(("xoa", dict(cu), vi_tri))
        return True, "Đã xóa " + ma_kh

    def hoan_tac(self):
        if not self.ngan_xep:
            return False, "Không còn thao tác để hoàn tác"
        thao_tac = self.ngan_xep.pop()
        if thao_tac[0] == "them":
            self.xoa(thao_tac[1], ghi_undo=False)
            return True, "Đã hoàn tác: thêm " + thao_tac[1]
        if thao_tac[0] == "xoa":
            _, r, vi_tri = thao_tac
            self.ds.insert(vi_tri, r)
            self._chi_muc_hoa(r)
            return True, "Đã hoàn tác: xóa " + r["ma_kh"]
        # còn lại là "sua": thay hồ sơ hiện tại bằng bản cũ
        r = thao_tac[1]
        hien_tai = self.chi_muc[r["ma_kh"]]
        vi_tri = self.ds.index(hien_tai)
        self._go_chi_muc(hien_tai)
        self.ds[vi_tri] = r
        self._chi_muc_hoa(r)
        return True, "Đã hoàn tác: sửa " + r["ma_kh"]

    def sap_xep(self, theo="ho_ten", giam_dan=False):
        if theo == "ho_ten":
            # người Việt gọi theo tên nên xếp theo tên (từ cuối) trước, rồi mới đến cả họ tên
            def khoa(kh):
                tu = bo_dau(kh["ho_ten"]).split()
                return (tu[-1], bo_dau(kh["ho_ten"]))
        elif theo in ("so_du", "ngay_dk", "ma_kh"):
            def khoa(kh):
                return kh[theo]
        else:
            raise ValueError("Tiêu chí sắp xếp không hợp lệ: " + str(theo))
        return sap_xep_tron(self.ds, khoa, giam_dan)

    def top_k_so_du(self, k):
        """Top-k số dư lớn nhất bằng heap, O(n log k)."""
        if k <= 0:
            return []
        return heapq.nlargest(k, self.ds, key=lambda kh: kh["so_du"])

    def thong_ke(self, theo="loai_kh"):
        nhom = {}
        for kh in self.ds:
            m = nhom.setdefault(kh[theo], {"so_luong": 0, "tong_so_du": 0.0})
            m["so_luong"] += 1
            m["tong_so_du"] += kh["so_du"]
        return nhom

    def ghi_csv(self, duong_dan):
        with open(duong_dan, "w", newline="", encoding="utf-8-sig") as f:
            w = csv.DictWriter(f, fieldnames=self.TRUONG)
            w.writeheader()
            for kh in self.ds:
                row = dict(kh)
                row["ngay_dk"] = str(row["ngay_dk"])
                w.writerow(row)

    def doc_csv(self, duong_dan):
        them_duoc = 0
        loi = []
        with open(duong_dan, newline="", encoding="utf-8-sig") as f:
            for dong, row in enumerate(csv.DictReader(f), start=2):   # dòng 1 là tiêu đề
                try:
                    row["ngay_dk"] = date.fromisoformat(row["ngay_dk"])
                except (ValueError, KeyError):
                    loi.append((dong, "Ngày đăng ký không hợp lệ"))
                    continue
                ok, msg = self.them(row)
                if ok:
                    them_duoc += 1
                else:
                    loi.append((dong, msg))
        return them_duoc, loi


HO = ["Nguyễn", "Trần", "Lê", "Phạm", "Hoàng", "Huỳnh", "Phan", "Vũ", "Võ", "Đặng", "Bùi", "Đỗ", "Hồ", "Ngô", "Dương"]
DEM = ["Văn", "Thị", "Minh", "Quốc", "Thanh", "Ngọc", "Hữu", "Anh", "Gia", "Thu", "Đức", "Hoài"]
TEN = ["An", "Bình", "Châu", "Dũng", "Giang", "Hà", "Hùng", "Khánh", "Lan", "Linh", "Mai", "Nam",
       "Phúc", "Quân", "Sơn", "Thảo", "Trang", "Tuấn", "Vy", "Yến", "Ân", "Đạt", "Oanh", "Hiếu"]
DIA_PHUONG = ["TP. Hồ Chí Minh", "Hà Nội", "Đà Nẵng", "Cần Thơ", "Hải Phòng",
              "Đồng Nai", "Bình Dương", "Khánh Hòa", "Lâm Đồng", "Nghệ An"]


def sinh_du_lieu(n, hat_giong=42):
    """Sinh n khách hàng giả. Dùng seed cố định để chạy lại ra đúng kết quả cũ."""
    rd = random.Random(hat_giong)
    rd2 = random.Random(hat_giong + 1)     # bộ sinh riêng cho điểm tín dụng, để dữ liệu cũ không bị đổi
    ds = []
    ngay_dau = date(2015, 1, 1)
    so_ngay = (date(2026, 9, 30) - ngay_dau).days
    cccd_set = rd.sample(range(10**11, 10**12), n)      # sample để không bị trùng
    sdt_set = rd.sample(range(10**8, 10**9), n)
    for i in range(n):
        ten = rd.choice(HO) + " " + rd.choice(DEM) + " " + rd.choice(TEN)
        loai = rd.choices(["Thường", "VIP", "Doanh nghiệp"], weights=[80, 15, 5])[0]
        he_so = {"Thường": 1, "VIP": 8, "Doanh nghiệp": 25}[loai]
        so_du = round(rd.lognormvariate(16.0, 1.0) * he_so / 10) * 10
        ds.append({
            "ma_kh": "KH%06d" % (i + 1),
            "ho_ten": ten,
            "cccd": "%012d" % cccd_set[i],
            "sdt": "0%09d" % sdt_set[i],
            "email": bo_dau(ten).replace(" ", ".") + "." + str(i + 1) + "@mail.test",
            "dia_phuong": rd.choice(DIA_PHUONG),
            "loai_kh": loai,
            "so_du": float(so_du),
            "ngay_dk": ngay_dau + timedelta(days=rd.randrange(so_ngay)),
            "diem_tin_dung": rd2.randint(300, 850),
            "is_vip": loai == "VIP",
        })
    return ds


def nap_he_thong(ds):
    ql = QuanLyKhachHang()
    for r in ds:
        ql.them(r, ghi_undo=False)
    return ql


def vnd(x):
    return f"{x:,.0f}".replace(",", ".")


# ============================================================================
# PHẦN 2: 28 CA KIỂM THỬ (copy từ notebook, gói vào 1 hàm)
# ============================================================================

def chay_kiem_thu():
    """Chạy 28 ca TC01-TC28, trả về danh sách kết quả."""
    ket_qua_test = []

    def mau(i=1, **kw):
        """Tạo 1 hồ sơ mẫu, các trường có thể ghi đè bằng kw."""
        r = {"ma_kh": "KH%06d" % i, "ho_ten": "Nguyễn Văn An", "cccd": "0790%08d" % i,
             "sdt": "09%08d" % i, "email": "an%d@mail.test" % i, "dia_phuong": "Hà Nội",
             "loai_kh": "Thường", "so_du": 1000000, "ngay_dk": date(2024, 1, 15),
             "diem_tin_dung": 700, "is_vip": False}
        r.update(kw)
        return r

    def tc(ma, mo_ta, dau_vao, mong_doi, ham):
        try:
            ok, ghi_chu = ham()
            ket_qua_test.append({"ma": ma, "mo_ta": mo_ta, "dau_vao": dau_vao,
                                 "mong_doi": mong_doi, "thuc_te": ghi_chu, "dat": bool(ok)})
        except Exception as e:
            ket_qua_test.append({"ma": ma, "mo_ta": mo_ta, "dau_vao": dau_vao,
                                 "mong_doi": mong_doi, "thuc_te": "Lỗi: " + repr(e), "dat": False})

    # ---- nhóm A: thêm, kiểm tra hợp lệ, trùng ----
    def t01():
        ql = QuanLyKhachHang()
        ok = (len(ql.ds) == 0 and ql.tra_cuu("KH000001") is None and ql.sap_xep() == []
              and ql.top_k_so_du(3) == [] and ql.tim_theo_ten("n") == [] and ql.thong_ke() == {}
              and ql.hoan_tac()[0] is False)
        return ok, "Mọi thao tác trên danh sách rỗng đều trả về rỗng/None, không báo lỗi"
    tc("TC01", "Danh sách rỗng", "Chưa có khách hàng; gọi tra cứu, sắp xếp, Top-k, tìm tiền tố, thống kê, hoàn tác",
       "Không phát sinh lỗi; kết quả rỗng/None", t01)

    def t02():
        ql = QuanLyKhachHang()
        ok, m = ql.them(mau(1))
        dung = (ok and len(ql) == 1 and ql.sap_xep()[0]["ma_kh"] == "KH000001"
                and ql.top_k_so_du(5)[0]["ma_kh"] == "KH000001" and tim_nhi_phan(ql.ds, "KH000001") is not None)
        return dung, m + "; sắp xếp, Top-5, tìm nhị phân đều trả về đúng 1 bản ghi"
    tc("TC02", "Chỉ có một phần tử", "Thêm 1 khách hàng rồi sắp xếp, Top-5, tìm nhị phân",
       "Trả về đúng 1 bản ghi", t02)

    def t03():
        ql = QuanLyKhachHang()
        ql.them(mau(1))
        ok, m = ql.them(mau(1, cccd="079099999999", sdt="0911111111", email="khac@mail.test"))
        return (not ok and m == "Trùng mã khách hàng" and len(ql) == 1), "Từ chối: '" + m + "'; số bản ghi vẫn = " + str(len(ql))
    tc("TC03", "Trùng mã khách hàng", "Thêm KH000001 lần thứ hai (các trường khác đều khác)", "Từ chối, báo trùng mã", t03)

    def t04():
        ql = QuanLyKhachHang()
        ql.them(mau(1))
        ok, m = ql.them(mau(2, cccd=mau(1)["cccd"]))
        return (not ok and m == "Trùng CCCD"), "Từ chối: '" + m + "'"
    tc("TC04", "Trùng CCCD", "Thêm KH000002 có CCCD trùng KH000001", "Từ chối, báo trùng CCCD", t04)

    def t05():
        ql = QuanLyKhachHang()
        ql.them(mau(1))
        ok1, m1 = ql.them(mau(2, sdt=mau(1)["sdt"]))
        ok2, m2 = ql.them(mau(3, email=mau(1)["email"].upper()))
        dung = (not ok1 and m1 == "Trùng số điện thoại" and not ok2 and m2 == "Trùng email")
        return dung, "SĐT: '" + m1 + "'; email viết hoa: '" + m2 + "' (email được đổi về chữ thường trước khi so)"
    tc("TC05", "Trùng SĐT và trùng email", "SĐT trùng; email trùng nhưng viết HOA", "Từ chối cả hai, đúng lý do", t05)

    def t06():
        ql = QuanLyKhachHang()
        ok, m = ql.them(mau(1, so_du=-500000))
        return (not ok and m == "Số dư âm" and len(ql) == 0), "Từ chối: '" + m + "'"
    tc("TC06", "Số dư âm", "so_du = -500.000", "Từ chối, báo số dư âm", t06)

    def t07():
        ql = QuanLyKhachHang()
        kq = [ql.them(mau(1, cccd="12345"))[1],
              ql.them(mau(2, sdt="123"))[1],
              ql.them(mau(3, email="abc"))[1],
              ql.them(mau(4, loai_kh="Khác"))[1],
              ql.them(mau(5, ho_ten=""))[1],
              ql.them(mau(6, so_du="abc"))[1]]
        dung = ["CCCD phải gồm 12 chữ số", "SĐT phải gồm 10 chữ số, bắt đầu bằng 0", "Email không đúng định dạng",
                "Loại khách hàng không hợp lệ", "Thiếu trường 'ho_ten'", "Thiếu trường 'so_du'"]
        return (kq == dung and len(ql) == 0), "Từ chối đủ 6 trường hợp: " + " | ".join(kq)
    tc("TC07", "Dữ liệu sai định dạng hoặc thiếu",
       "CCCD 5 số; SĐT 3 số; email 'abc'; loại 'Khác'; họ tên rỗng; số dư 'abc'",
       "Từ chối, báo đúng từng lý do", t07)

    def t08():
        ql = QuanLyKhachHang()
        ok, m = ql.them(mau(1, ma_kh="  kh000001 ", ho_ten="  Nguyễn   Văn  An ", email="AN1@Mail.TEST"))
        kh = ql.tra_cuu("kh000001")
        dung = (ok and kh["ma_kh"] == "KH000001" and kh["ho_ten"] == "Nguyễn Văn An" and kh["email"] == "an1@mail.test")
        return dung, "Đã chuẩn hóa: mã='" + kh["ma_kh"] + "', họ tên='" + kh["ho_ten"] + "', email='" + kh["email"] + "'"
    tc("TC08", "Chuẩn hóa dữ liệu nhập",
       "Mã '  kh000001 ' (thừa khoảng trắng, chữ thường); họ tên thừa khoảng trắng; email có chữ hoa",
       "Lưu dạng chuẩn hóa", t08)

    # ---- nhóm B: tra cứu ----
    def t09():
        ql = nap_he_thong(sinh_du_lieu(100))
        kh = ql.tra_cuu("KH000050")
        dung = (kh is not None and kh["ma_kh"] == "KH000050" and tim_tuan_tu(ql.ds, "KH000050") is kh)
        return dung, "Trả về " + kh["ma_kh"] + " - " + kh["ho_ten"] + "; kết quả của dict và Linear Search trùng nhau"
    tc("TC09", "Mã tồn tại", "Tra cứu KH000050 trong 100 hồ sơ", "Trả về đúng hồ sơ", t09)

    def t10():
        ql = nap_he_thong(sinh_du_lieu(100))
        s = sorted(ql.ds, key=lambda k: k["ma_kh"])
        a = ql.tra_cuu("KH999999")
        b = tim_tuan_tu(ql.ds, "KH999999")
        c = tim_nhi_phan(s, "KH999999")
        return (a is None and b is None and c is None), f"dict -> {a}; Linear Search -> {b}; Binary Search -> {c}"
    tc("TC10", "Khóa không tồn tại", "Tra cứu KH999999 bằng 3 phương pháp", "Cả ba trả về None", t10)

    def t11():
        ql = nap_he_thong(sinh_du_lieu(1000))
        s = sorted(ql.ds, key=lambda k: k["ma_kh"])
        ok1 = all(tim_nhi_phan(s, k["ma_kh"]) is k for k in ql.ds)
        ok2 = all(ql.tra_cuu(k["ma_kh"]) is k for k in ql.ds)
        return (ok1 and ok2), "1.000/1.000 mã đều được Binary Search và dict tìm thấy đúng (kể cả phần tử đầu và cuối)"
    tc("TC11", "Đối chiếu 3 phương pháp tra cứu", "Mọi mã trong 1.000 hồ sơ", "Binary Search = dict = Linear Search", t11)

    def t12():
        ql = QuanLyKhachHang()
        ten_mau = ["Nguyễn Văn An", "Trần Thị Ân", "Lê Minh Anh", "Phạm Quốc Bình", "Đặng Hoài An"]
        for i, ten in enumerate(ten_mau, start=1):
            ql.them(mau(i, ho_ten=ten))
        a = [k["ho_ten"] for k in ql.tim_theo_ten("an")]
        b = [k["ho_ten"] for k in ql.tim_theo_ten("NGUYỄN")]
        c = [k["ho_ten"] for k in ql.tim_theo_ten("zzz")]
        d = [k["ho_ten"] for k in ql.tim_theo_ten("van an")]
        dung = (a == ["Nguyễn Văn An", "Trần Thị Ân", "Lê Minh Anh", "Đặng Hoài An"] and b == ["Nguyễn Văn An"]
                and c == [] and d == ["Nguyễn Văn An"])
        return dung, f"'an' -> {len(a)} KH (An, Ân, Anh đều khớp vì đã bỏ dấu); 'NGUYỄN' -> {b}; 'zzz' -> {c}; 'van an' -> {d}"
    tc("TC12", "Gợi ý theo tiền tố (Trie)", "Tiền tố 'an', 'NGUYỄN', 'zzz', 'van an' trên 5 họ tên có dấu",
       "Không phân biệt hoa/thường, dấu; không khớp thì trả về rỗng", t12)

    def t13():
        ql = QuanLyKhachHang()
        ql.them(mau(1, dia_phuong="Hà Nội", loai_kh="VIP", so_du=500000000))
        ql.them(mau(2, dia_phuong="Hà Nội", loai_kh="Thường", so_du=10000000))
        ql.them(mau(3, dia_phuong="Đà Nẵng", loai_kh="VIP", so_du=200000000))
        a = [k["ma_kh"] for k in ql.loc(dia_phuong="Hà Nội", loai_kh="VIP")]
        b = [k["ma_kh"] for k in ql.loc(so_du_tu=100000000, so_du_den=300000000)]
        c = ql.loc(dia_phuong="Cần Thơ")
        return (a == ["KH000001"] and b == ["KH000003"] and c == []), f"Hà Nội + VIP -> {a}; số dư 100-300 triệu -> {b}; Cần Thơ -> {c}"
    tc("TC13", "Lọc nhiều điều kiện", "(Hà Nội, VIP); số dư 100-300 triệu; địa phương không có KH",
       "Trả về đúng tập hợp", t13)

    # ---- nhóm C: sắp xếp ----
    def t14():
        ql = nap_he_thong(sinh_du_lieu(500))
        tang = ql.sap_xep("so_du")
        giam = ql.sap_xep("so_du", giam_dan=True)
        dung = (all(tang[i]["so_du"] <= tang[i + 1]["so_du"] for i in range(len(tang) - 1))
                and all(giam[i]["so_du"] >= giam[i + 1]["so_du"] for i in range(len(giam) - 1))
                and [k["so_du"] for k in tang] == sorted(k["so_du"] for k in ql.ds))
        return dung, "Tăng dần/giảm dần đúng thứ tự và trùng với sorted() của Python"
    tc("TC14", "Sắp xếp theo số dư (dữ liệu ngẫu nhiên)", "500 hồ sơ, tăng dần và giảm dần",
       "Đúng thứ tự, khớp với sorted()", t14)

    def t15():
        ql = nap_he_thong(sinh_du_lieu(300))
        ds0 = [k["ma_kh"] for k in ql.ds]
        da_sap = ql.sap_xep("ma_kh")
        ql2 = QuanLyKhachHang()
        for k in da_sap:
            ql2.them(k, ghi_undo=False)
        xuoi = ql2.sap_xep("ma_kh")
        nguoc = sap_xep_tron(da_sap[::-1], key=lambda k: k["ma_kh"])
        dung = ([k["ma_kh"] for k in xuoi] == [k["ma_kh"] for k in da_sap]
                and [k["ma_kh"] for k in nguoc] == [k["ma_kh"] for k in da_sap]
                and [k["ma_kh"] for k in ql.ds] == ds0)
        return dung, "Dữ liệu đã có thứ tự và thứ tự ngược đều cho kết quả đúng; danh sách gốc không bị đổi"
    tc("TC15", "Dữ liệu đã có thứ tự / thứ tự ngược", "300 hồ sơ đã sắp theo mã; đảo ngược rồi sắp lại",
       "Kết quả đúng; dữ liệu gốc giữ nguyên", t15)

    def t16():
        ql = QuanLyKhachHang()
        ten_mau = ["Trần Văn Bình", "Nguyễn Thị An", "Đặng Quốc An", "Lê Minh Ân", "Phạm Hoài Anh"]
        for i, ten in enumerate(ten_mau, start=1):
            ql.them(mau(i, ho_ten=ten))
        kq = [k["ho_ten"] for k in ql.sap_xep("ho_ten")]
        dung = ["Đặng Quốc An", "Lê Minh Ân", "Nguyễn Thị An", "Phạm Hoài Anh", "Trần Văn Bình"]
        return kq == dung, "Thứ tự: " + " -> ".join(kq)
    tc("TC16", "Sắp xếp theo tên (tiếng Việt)", "5 họ tên có dấu, trùng tên 'An'/'Ân'",
       "Xếp theo tên gọi rồi đến họ tên đầy đủ, không tính dấu", t16)

    def t17():
        ql = QuanLyKhachHang()
        for i, (m, sd) in enumerate([("A", 100), ("B", 100), ("C", 50), ("D", 100)], start=1):
            ql.them(mau(i, ho_ten="Nguyễn Văn " + m, so_du=sd))
        kq = [k["ma_kh"] for k in ql.sap_xep("so_du", giam_dan=True)]
        return kq == ["KH000001", "KH000002", "KH000004", "KH000003"], f"Giảm dần theo số dư, 3 KH cùng số dư 100 giữ nguyên thứ tự nhập: {kq}"
    tc("TC17", "Giá trị trùng khi sắp xếp (tính ổn định)", "3 KH cùng số dư 100 và 1 KH số dư 50",
       "Giữ nguyên thứ tự nhập giữa các KH cùng số dư", t17)

    def t18():
        ql = nap_he_thong(sinh_du_lieu(2000))
        top = ql.top_k_so_du(5)
        chuan = sorted(ql.ds, key=lambda k: k["so_du"], reverse=True)[:5]
        ql_nho = QuanLyKhachHang()
        ql_nho.them(mau(1))
        ql_nho.them(mau(2, ho_ten="B"))
        dung = ([k["ma_kh"] for k in top] == [k["ma_kh"] for k in chuan]
                and len(ql.top_k_so_du(0)) == 0 and len(ql_nho.top_k_so_du(10)) == 2)
        return dung, "Top-5 trùng với kết quả sắp xếp toàn bộ; k=0 -> rỗng; k lớn hơn n -> trả về n bản ghi"
    tc("TC18", "Top-k bằng heap", "k=5 trên 2.000 hồ sơ; k=0; k=10 trên 2 hồ sơ", "Đúng thứ tự, xử lý đúng k biên", t18)

    # ---- nhóm D: sửa, xóa, hoàn tác, thống kê, CSV ----
    def t19():
        ql = QuanLyKhachHang()
        for i in (1, 2, 3):
            ql.them(mau(i, ho_ten="Nguyễn Văn " + "ABC"[i - 1]))
        ok1, _ = ql.sua("KH000002", so_du=9999999, loai_kh="VIP")
        ok2, m2 = ql.sua("KH000002", cccd=mau(1)["cccd"])
        ok3, m3 = ql.sua("KH000099", so_du=1)
        ok4, _ = ql.sua("KH000002", cccd=mau(2)["cccd"])      # giữ nguyên CCCD của chính mình thì vẫn được
        kh = ql.tra_cuu("KH000002")
        dung = (ok1 and not ok2 and m2 == "Trùng CCCD" and not ok3 and ok4
                and kh["so_du"] == 9999999 and kh["loai_kh"] == "VIP")
        return dung, f"Sửa hợp lệ -> được; sửa sang CCCD của người khác -> '{m2}'; sửa mã không tồn tại -> '{m3}'"
    tc("TC19", "Sửa hồ sơ", "Sửa số dư/loại; sửa CCCD trùng người khác; sửa mã không tồn tại; giữ nguyên CCCD của chính mình",
       "Chỉ chấp nhận thay đổi hợp lệ", t19)

    def t20():
        ql = QuanLyKhachHang()
        ql.them(mau(1, ho_ten="Nguyễn Văn An"))
        ql.them(mau(2, ho_ten="Trần Thị Bình"))
        ok1, _ = ql.xoa("KH000001")
        sau_xoa = (ql.tra_cuu("KH000001") is None and len(ql) == 1 and ql.tim_theo_ten("nguyen") == [])
        ok_lai, m = ql.them(mau(1, ho_ten="Nguyễn Văn An"))     # xóa rồi thì CCCD/SĐT/email được giải phóng
        ok2, m2 = ql.xoa("KH000077")
        return (ok1 and sau_xoa and ok_lai and not ok2), f"Xóa xong: tra cứu = None, Trie không còn tên; thêm lại cùng CCCD/SĐT/email -> '{m}'; xóa mã không tồn tại -> '{m2}'"
    tc("TC20", "Xóa hồ sơ và giải phóng chỉ mục", "Xóa KH000001 rồi thêm lại; xóa mã không tồn tại",
       "dict/set/Trie được cập nhật đồng bộ", t20)

    def t21():
        ql = QuanLyKhachHang()
        ql.them(mau(1))
        ql.them(mau(2, ho_ten="Trần Thị Bình"))
        ql.sua("KH000001", so_du=777)
        ql.xoa("KH000002")
        b1 = ql.hoan_tac()[1]
        c1 = ql.tra_cuu("KH000002") is not None and ql.tim_theo_ten("binh") != []
        b2 = ql.hoan_tac()[1]
        c2 = ql.tra_cuu("KH000001")["so_du"] == 1000000
        b3 = ql.hoan_tac()[1]
        c3 = ql.tra_cuu("KH000002") is None
        b4 = ql.hoan_tac()[1]
        c4 = len(ql) == 0
        ok5, b5 = ql.hoan_tac()
        return (c1 and c2 and c3 and c4 and not ok5), "Đúng thứ tự LIFO: " + " -> ".join([b1, b2, b3, b4]) + " -> khi stack rỗng: '" + b5 + "'"
    tc("TC21", "Hoàn tác (Stack)", "Thêm, thêm, sửa, xóa rồi hoàn tác 5 lần",
       "Khôi phục theo thứ tự ngược; hết thao tác thì báo, không lỗi", t21)

    def t22():
        ql = nap_he_thong(sinh_du_lieu(1000))
        tk = ql.thong_ke("loai_kh")
        tk2 = ql.thong_ke("dia_phuong")
        tong = sum(v["so_luong"] for v in tk.values())
        tong2 = sum(v["so_luong"] for v in tk2.values())
        tong_sd = sum(v["tong_so_du"] for v in tk.values())
        dung = (tong == 1000 and tong2 == 1000 and abs(tong_sd - sum(k["so_du"] for k in ql.ds)) < 1e-6)
        return dung, f"Tổng số KH theo loại = {tong}, theo địa phương = {tong2} (đều bằng 1.000); tổng số dư khớp"
    tc("TC22", "Thống kê theo nhóm", "1.000 hồ sơ, theo loại KH và địa phương", "Tổng các nhóm = tổng toàn bộ", t22)

    def t23():
        ql = nap_he_thong(sinh_du_lieu(200))
        ql.ghi_csv("kh.csv")
        ql2 = QuanLyKhachHang()
        n, loi = ql2.doc_csv("kh.csv")
        with open("kh_loi.csv", "w", encoding="utf-8-sig") as f:
            f.write(",".join(QuanLyKhachHang.TRUONG) + "\n")
            f.write("KH900001,An,079000000001,0900000001,a@mail.test,Hà Nội,Thường,100,2024-01-01,700,False\n")   # đúng
            f.write("KH900001,An,079000000002,0900000002,b@mail.test,Hà Nội,Thường,100,2024-01-01,700,False\n")   # trùng mã
            f.write("KH900003,An,079000000003,0900000003,c@mail.test,Hà Nội,Thường,100,01/01/2024,700,False\n")   # sai định dạng ngày
        ql3 = QuanLyKhachHang()
        n3, loi3 = ql3.doc_csv("kh_loi.csv")
        dung = (n == 200 and loi == [] and [k["ma_kh"] for k in ql2.ds] == [k["ma_kh"] for k in ql.ds]
                and n3 == 1 and len(loi3) == 2)
        return dung, f"Ghi rồi đọc lại 200/200 hồ sơ, không lỗi; file có 3 dòng (1 đúng, 1 trùng mã, 1 sai ngày) -> thêm {n3}, báo lỗi: {loi3}"
    tc("TC23", "Đọc/ghi CSV", "Ghi 200 hồ sơ rồi đọc lại; đọc file có dòng lỗi",
       "Dữ liệu nguyên vẹn; dòng lỗi được báo số dòng, chương trình không dừng", t23)

    def t24():
        ds = sinh_du_lieu(1000)
        ds[500]["cccd"] = ds[10]["cccd"]
        ds[900]["cccd"] = ds[10]["cccd"]
        a = trung_hai_vong_lap(ds)
        b = trung_bang_set(ds)
        dung = (len(a) == 3 and len(b) == 2 and {x for p in b for x in p} <= {x for p in a for x in p})
        return dung, f"2 vòng lặp: {len(a)} cặp trùng (mọi cặp); set: {len(b)} bản ghi trùng so với bản đầu tiên, cùng chỉ ra đúng 3 hồ sơ liên quan"
    tc("TC24", "Phát hiện CCCD trùng: 2 vòng lặp và set", "1.000 hồ sơ, cố ý gán cùng 1 CCCD cho 3 hồ sơ",
       "Hai cách cùng chỉ ra 3 hồ sơ trùng", t24)


    # ---- nhóm E: điểm tín dụng, is_vip và hàng đợi VIP ----
    def t25():
        ql = QuanLyKhachHang()
        thap = ql.them(mau(1, diem_tin_dung=149))[1]
        cao = ql.them(mau(2, diem_tin_dung=751))[1]
        chu = ql.them(mau(3, diem_tin_dung="abc"))[1]
        bien1, _ = ql.them(mau(4, diem_tin_dung=150))
        bien2, _ = ql.them(mau(5, diem_tin_dung="50"))
        vip_chuoi, _ = ql.them(mau(6, is_vip="True"))
        sai_vip = ql.them(mau(7, is_vip="abc"))[1]
        dung = (thap == cao == "Điểm tín dụng phải nằm trong khoảng 300-850" and chu == "Thiếu trường 'diem_tin_dung'"
                and bien1 and bien2 and vip_chuoi and ql.tra_cuu("KH000006")["is_vip"] is True
                and sai_vip == "Thiếu trường 'is_vip'" and len(ql) == 3)
        return dung, f"299 và 851 bị từ chối: '{thap}'; 'abc' -> '{chu}'; biên 300 và 850 được nhận; is_vip='True' đọc thành True; is_vip='abc' -> '{sai_vip}'"
    tc("TC25", "Trường diem_tin_dung và is_vip", "Điểm 299, 851, 'abc'; điểm biên 300 và 850; is_vip dạng chuỗi 'True' và 'abc'",
       "Từ chối điểm ngoài [300, 850]; nhận điểm biên; đọc đúng is_vip", t25)

    def t26():
        ql = QuanLyKhachHang()
        ql.them(mau(1, ho_ten="Khách thường"))                                           # không VIP, dưới 1 tỷ -> không vào
        ql.them(mau(2, ho_ten="VIP số dư thấp", is_vip=True, so_du=50000000, diem_tin_dung=800))
        ql.them(mau(3, ho_ten="Đủ 1 tỷ", so_du=1000000000, diem_tin_dung=500))            # không đánh dấu nhưng đủ 1 tỷ -> vào
        ql.them(mau(4, ho_ten="VIP trùng số dư A", is_vip=True, so_du=50000000, diem_tin_dung=700))
        ql.them(mau(5, ho_ten="VIP trùng số dư B", is_vip=True, so_du=50000000, diem_tin_dung=800))
        ql.them(mau(6, ho_ten="VIP số dư lớn nhất", is_vip=True, so_du=2000000000, diem_tin_dung=400))
        thu_tu = [k["ma_kh"] for k in ql.xem_hang_doi_vip(10)]
        dung = (thu_tu == ["KH000006", "KH000003", "KH000002", "KH000005", "KH000004"]
                and ql.so_luong_vip() == 5 and len(ql.xem_hang_doi_vip(10)) == 5)
        return dung, f"Thứ tự: {thu_tu} (số dư giảm dần; cùng số dư thì điểm tín dụng cao hơn trước; KH000001 không vào hàng đợi); xem xong hàng đợi vẫn đủ 5 khách"
    tc("TC26", "Hàng đợi VIP: tiêu chí vào và thứ tự ưu tiên",
       "6 khách: 1 thường; 1 VIP số dư thấp; 1 chưa đánh dấu nhưng đủ 1 tỷ; 2 VIP cùng số dư khác điểm tín dụng; 1 VIP số dư 2 tỷ",
       "Chỉ khách VIP hoặc từ 1 tỷ vào hàng đợi; xếp theo số dư, rồi điểm tín dụng", t26)

    def t27():
        ql = QuanLyKhachHang()
        ql.them(mau(1, is_vip=True, so_du=300000000))
        ql.them(mau(2, is_vip=True, so_du=200000000))
        ql.them(mau(3, is_vip=True, so_du=100000000))
        ql.sua("KH000003", so_du=900000000)                  # KH000003 vươn lên đầu hàng
        a = [k["ma_kh"] for k in ql.xem_hang_doi_vip(5)]
        ql.xoa("KH000001")                                   # xóa hồ sơ thì rời hàng đợi
        b = [k["ma_kh"] for k in ql.xem_hang_doi_vip(5)]
        ql.sua("KH000002", is_vip=False)                     # mất đánh dấu và dưới 1 tỷ -> rời hàng đợi
        c = [k["ma_kh"] for k in ql.xem_hang_doi_vip(5)]
        ql.hoan_tac()                                        # hoàn tác lần sửa cuối
        d = [k["ma_kh"] for k in ql.xem_hang_doi_vip(5)]
        ql.hoan_tac()                                        # hoàn tác lần xóa
        e = [k["ma_kh"] for k in ql.xem_hang_doi_vip(5)]
        dung = (a == ["KH000003", "KH000001", "KH000002"] and b == ["KH000003", "KH000002"]
                and c == ["KH000003"] and d == ["KH000003", "KH000002"] and e == ["KH000003", "KH000001", "KH000002"]
                and ql.so_luong_vip() == 3)
        return dung, f"Sau sửa số dư: {a}; sau xóa KH000001: {b}; sau sửa is_vip=False: {c}; hoàn tác 2 lần: {d} rồi {e}"
    tc("TC27", "Hàng đợi VIP khi sửa, xóa và hoàn tác", "Sửa số dư; xóa hồ sơ; bỏ đánh dấu VIP; hoàn tác 2 lần",
       "Hàng đợi luôn khớp dữ liệu hiện tại, không còn khách đã xóa hay hết điều kiện", t27)

    def t28():
        ql = QuanLyKhachHang()
        n_rong = (ql.phuc_vu_vip() is None and ql.xem_hang_doi_vip(3) == [])
        ql = nap_he_thong(sinh_du_lieu(1000))
        chuan = sorted((k for k in ql.ds if k["is_vip"] or k["so_du"] >= NGUONG_VIP),
                       key=lambda k: (-k["so_du"], -k["diem_tin_dung"]))
        so_vip = len(chuan)
        thu_tu = []
        while True:
            kh = ql.phuc_vu_vip()
            if kh is None:
                break
            thu_tu.append(kh["ma_kh"])
        dung = (n_rong and thu_tu == [k["ma_kh"] for k in chuan] and ql.so_luong_vip() == 0
                and len(ql) == 1000 and ql.phuc_vu_vip() is None)
        return dung, f"Hàng đợi rỗng -> None; 1.000 hồ sơ có {so_vip} khách ưu tiên, phục vụ lần lượt đúng thứ tự khi sắp xếp toàn bộ; sau khi phục vụ hết vẫn còn {len(ql)} hồ sơ"
    tc("TC28", "Phục vụ khách VIP (lấy ra khỏi hàng đợi)", "Hàng đợi rỗng; 1.000 hồ sơ mô phỏng phục vụ đến hết",
       "Đúng thứ tự ưu tiên; hết khách trả về None; hồ sơ không bị xóa", t28)
    return ket_qua_test


# ============================================================================
# PHẦN 3: ĐO HIỆU NĂNG (giống ô "Thực nghiệm hiệu năng" trong notebook)
# ============================================================================

def do(ham, so_lan):
    """Chạy ham() so_lan lần, trả về (trung bình, độ lệch chuẩn) tính bằng giây."""
    t = []
    for _ in range(so_lan):
        a = time.perf_counter()
        ham()
        t.append(time.perf_counter() - a)
    return statistics.mean(t), (statistics.stdev(t) if len(t) > 1 else 0.0)


def chay_hieu_nang(kich_thuoc, bao_tien_do=None):
    perf = {"tra_cuu": {}, "sap_xep": {}, "trung": {}, "top_k": {}, "tien_to": {}}
    bo_nho = {}
    for stt, n in enumerate(kich_thuoc):
        ds = sinh_du_lieu(n)
        ql = nap_he_thong(ds)
        s_ma = sorted(ds, key=lambda k: k["ma_kh"])
        rd = random.Random(1)
        # 200 mã để tra: 100 mã có thật + 100 mã không có
        truy_van = [rd.choice(ds)["ma_kh"] for _ in range(100)] + ["KX%06d" % i for i in range(100)]
        nhieu = 3 if n >= 10000 else 5

        perf["tra_cuu"][n] = {
            "Linear Search (list)": do(lambda: [tim_tuan_tu(ds, m) for m in truy_van], nhieu),
            "Binary Search (list đã sắp)": do(lambda: [tim_nhi_phan(s_ma, m) for m in truy_van], 20),
            "Dictionary (Hash)": do(lambda: [ql.tra_cuu(m) for m in truy_van], 20),
        }
        key_sd = lambda k: k["so_du"]
        perf["sap_xep"][n] = {
            "Insertion Sort O(n²)": do(lambda: sap_xep_chen(ds, key_sd), nhieu),
            "Merge Sort tự cài O(n log n)": do(lambda: sap_xep_tron(ds, key_sd), 5),
            "sorted() của Python (Timsort)": do(lambda: sorted(ds, key=key_sd), 20),
        }
        perf["trung"][n] = {
            "Hai vòng lặp O(n²)": do(lambda: trung_hai_vong_lap(ds), nhieu),
            "Dùng set/dict O(n)": do(lambda: trung_bang_set(ds), 20),
        }
        perf["top_k"][n] = {
            "Sắp xếp toàn bộ rồi lấy 10": do(lambda: sorted(ds, key=key_sd, reverse=True)[:10], 20),
            "Heap (nlargest) O(n log k)": do(lambda: ql.top_k_so_du(10), 20),
        }
        tien_to = ["an", "nguyen van", "tran thi", "le minh", "pham"]

        def quet():
            # cách thủ công: duyệt cả list, bỏ dấu từng tên rồi so tiền tố
            for tt in tien_to:
                kq = []
                for k in ds:
                    tu = bo_dau(k["ho_ten"]).split()
                    for i in range(3):
                        if " ".join(tu[i:]).startswith(tt):
                            kq.append(k)
                            break
        perf["tien_to"][n] = {
            "Quét tuần tự toàn bộ list": do(quet, nhieu),
            "Trie": do(lambda: [ql.tim_theo_ten(tt) for tt in tien_to], 20),
        }

        # đo bộ nhớ và thời gian dựng chỉ mục
        tracemalloc.start()
        nap_he_thong(ds)
        cur, _ = tracemalloc.get_traced_memory()
        tracemalloc.stop()
        t0 = time.perf_counter()
        nap_he_thong(ds)
        bo_nho[n] = {"mb": cur / 1e6, "giay_nap": time.perf_counter() - t0}

        if bao_tien_do:
            bao_tien_do((stt + 1) / len(kich_thuoc), n)
    return perf, bo_nho


TEN_NHOM = {"tra_cuu": "Tra cứu theo mã (200 truy vấn/lần đo)",
            "sap_xep": "Sắp xếp theo số dư",
            "trung": "Phát hiện CCCD trùng",
            "top_k": "Top-10 số dư lớn nhất",
            "tien_to": "Tìm theo tiền tố (5 tiền tố/lần đo)"}

# ============================================================================
# PHẦN 4: GIAO DIỆN WEB (Streamlit)
# ============================================================================
import streamlit as st
import pandas as pd
import matplotlib.pyplot as plt

st.set_page_config(page_title="Quản lý khách hàng ngân hàng", layout="wide")

st.markdown("""
<style>
.block-container {padding-top: 1.5rem;}
h1, h2, h3 {color: #0b5d5b;}
</style>""", unsafe_allow_html=True)

TEN_COT = {"ma_kh": "Mã KH", "ho_ten": "Họ tên", "cccd": "CCCD", "sdt": "SĐT",
           "email": "Email", "dia_phuong": "Địa phương", "loai_kh": "Loại KH",
           "so_du": "Số dư (VND)", "ngay_dk": "Ngày ĐK",
           "diem_tin_dung": "Điểm TD", "is_vip": "Đánh dấu VIP"}
CAU_HINH_SO_DU = {"Số dư (VND)": st.column_config.NumberColumn(format="%,.0f")}
DS_LOAI = ["Thường", "VIP", "Doanh nghiệp"]      # thứ tự hiển thị trong các ô chọn

# streamlit chạy lại cả file sau mỗi thao tác nên phải cất dữ liệu vào session_state
if "ql" not in st.session_state:
    st.session_state.ql = nap_he_thong(sinh_du_lieu(1000))
if "thong_bao" not in st.session_state:
    st.session_state.thong_bao = None
ql = st.session_state.ql


def bang(ds):
    df = pd.DataFrame(ds, columns=list(TEN_COT))
    df["ngay_dk"] = df["ngay_dk"].astype(str)
    return df.rename(columns=TEN_COT)


def bao(kq):
    ok, msg = kq
    if ok:
        st.success(msg)
    else:
        st.error(msg)


def ms(giay):
    return giay * 1000


# ---------------- thanh bên ----------------
with st.sidebar:
    st.title("Ngân hàng")
    st.caption("Đề tài 6 - Cấu trúc dữ liệu tài chính và giải thuật")
    st.metric("Tổng khách hàng", len(ql))
    st.metric("Thao tác có thể hoàn tác", len(ql.ngan_xep))
    if st.button("Hoàn tác (Stack)", width="stretch"):
        st.session_state.thong_bao = ql.hoan_tac()
        st.rerun()
    if st.button("Nạp lại 1.000 hồ sơ mẫu", width="stretch"):
        st.session_state.ql = nap_he_thong(sinh_du_lieu(1000))
        st.session_state.thong_bao = (True, "Đã nạp lại dữ liệu mẫu")
        st.rerun()
    st.divider()
    st.metric("Khách trong hàng đợi VIP", ql.so_luong_vip())
    st.markdown("**Cấu trúc dữ liệu**  \nlist, dict, set, Trie, Stack, Heap (Top-k và hàng đợi VIP)  \n**Giải thuật**  \nMerge Sort, Insertion Sort, Linear Search, Binary Search")

st.title("Quản lý thông tin khách hàng ngân hàng")

# thông báo kết quả thao tác hiện dạng toast để không làm các tab bị nhảy về tab đầu
if st.session_state.thong_bao:
    ok_tb, msg_tb = st.session_state.thong_bao
    st.toast(msg_tb, icon=":material/check_circle:" if ok_tb else ":material/error:")
    st.session_state.thong_bao = None

tab_ds, tab_them, tab_tk, tab_top, tab_vip, tab_csv, tab_ss, tab_test, tab_perf = st.tabs(
    ["Danh sách", "Thêm / Sửa / Xóa", "Thống kê", "Top-k", "Hàng đợi VIP", "CSV",
     "So sánh giải thuật", "Kiểm thử (28 ca)", "Hiệu năng"])

# ---------------- tab danh sách ----------------
with tab_ds:
    c1, c2, c3 = st.columns([2, 1, 1])
    che_do = c1.radio("Tìm theo", ["Tên (Trie, không cần dấu)", "Mã KH (dict)"], horizontal=True)
    tu_khoa = c1.text_input("Từ khóa", placeholder="vd: tran thi  hoặc  KH000001")
    loai = c2.selectbox("Loại KH", ["Tất cả"] + DS_LOAI)
    dp = c3.selectbox("Địa phương", ["Tất cả"] + DIA_PHUONG)
    s1, s2 = st.columns(2)
    sx = s1.selectbox("Sắp xếp theo", ["ho_ten", "so_du", "ngay_dk", "ma_kh"],
                      format_func=lambda x: TEN_COT[x])
    giam = s2.checkbox("Giảm dần")

    # sắp xếp toàn bộ bằng Merge Sort trước, rồi lọc (lọc không làm đổi thứ tự)
    ds = ql.sap_xep(sx, giam)
    if tu_khoa:
        if che_do.startswith("Tên"):
            tim = ql.tim_theo_ten(tu_khoa)
        else:
            kh = ql.tra_cuu(tu_khoa)
            tim = [kh] if kh else []
        ma_tim = {k["ma_kh"] for k in tim}
        ds = [k for k in ds if k["ma_kh"] in ma_tim]
    # lọc theo loại / địa phương bằng hàm loc()
    ma_loc = {k["ma_kh"] for k in ql.loc(dia_phuong=None if dp == "Tất cả" else dp,
                                         loai_kh=None if loai == "Tất cả" else loai)}
    ds = [k for k in ds if k["ma_kh"] in ma_loc]

    with st.expander("Lọc thêm theo khoảng số dư (hàm loc)"):
        d1, d2 = st.columns(2)
        sd_tu = d1.number_input("Số dư từ (VND)", min_value=0.0, value=0.0, step=1000000.0)
        sd_den = d2.number_input("Đến (VND, 0 = không giới hạn)", min_value=0.0, value=0.0, step=1000000.0)
        if sd_tu > 0 or sd_den > 0:
            ma_sd = {k["ma_kh"] for k in ql.loc(so_du_tu=sd_tu if sd_tu > 0 else None,
                                                so_du_den=sd_den if sd_den > 0 else None)}
            ds = [k for k in ds if k["ma_kh"] in ma_sd]

    st.caption(f"Hiển thị {len(ds)} / {len(ql)} khách hàng")
    st.dataframe(bang(ds), width="stretch", height=420, hide_index=True,
                 column_config=CAU_HINH_SO_DU)

# ---------------- tab thêm / sửa / xóa ----------------
with tab_them:
    st.subheader("Thêm khách hàng")
    with st.form("form_them"):
        a, b = st.columns(2)
        # gợi ý mã tiếp theo = số lớn nhất hiện có + 1 (không dùng len vì xóa rồi sẽ bị trùng)
        so_lon_nhat = max([int(k["ma_kh"][2:]) for k in ql.ds if k["ma_kh"][2:].isdigit()] or [0])
        ma = a.text_input("Mã KH", value="KH%06d" % (so_lon_nhat + 1))
        ten = b.text_input("Họ tên")
        cccd = a.text_input("CCCD (12 số)")
        sdt = b.text_input("SĐT (10 số, bắt đầu bằng 0)")
        email = a.text_input("Email")
        dia = b.selectbox("Địa phương", DIA_PHUONG)
        lk = a.selectbox("Loại KH", DS_LOAI)
        sd = b.number_input("Số dư (VND)", min_value=0.0, step=100000.0)
        nd = a.date_input("Ngày đăng ký", value=date.today())
        diem = b.number_input("Điểm tín dụng (150-750)", min_value=150, max_value=750, value=650, step=10)
        dau_vip = a.checkbox("Đánh dấu VIP")
        if st.form_submit_button("Thêm", type="primary"):
            st.session_state.thong_bao = ql.them({
                "ma_kh": ma, "ho_ten": ten, "cccd": cccd, "sdt": sdt, "email": email,
                "dia_phuong": dia, "loai_kh": lk, "so_du": sd, "ngay_dk": nd,
                "diem_tin_dung": diem, "is_vip": dau_vip})
            st.rerun()          # chạy lại để thanh bên cập nhật số liệu mới

    st.divider()
    st.subheader("Sửa / Xóa theo mã KH")
    ma_chon = st.text_input("Nhập mã KH cần thao tác", placeholder="KH000001").strip().upper()
    kh = ql.tra_cuu(ma_chon) if ma_chon else None
    if ma_chon and not kh:
        st.warning("Không tìm thấy mã này")
    if kh:
        ds_loai = DS_LOAI
        with st.form("form_sua"):
            a, b = st.columns(2)
            ten2 = a.text_input("Họ tên", kh["ho_ten"])
            sdt2 = b.text_input("SĐT", kh["sdt"])
            mail2 = a.text_input("Email", kh["email"])
            sd2 = b.number_input("Số dư (VND)", min_value=0.0, value=float(kh["so_du"]), step=100000.0)
            lk2 = a.selectbox("Loại KH", ds_loai, index=ds_loai.index(kh["loai_kh"]))
            dia2 = b.selectbox("Địa phương", DIA_PHUONG,
                               index=DIA_PHUONG.index(kh["dia_phuong"]) if kh["dia_phuong"] in DIA_PHUONG else 0)
            diem2 = a.number_input("Điểm tín dụng (300-850)", min_value=0, max_value=1000,
                                   value=int(kh["diem_tin_dung"]), step=10)
            vip2 = b.checkbox("Đánh dấu VIP", value=bool(kh["is_vip"]))
            if st.form_submit_button("Lưu thay đổi", type="primary"):
                st.session_state.thong_bao = ql.sua(
                    ma_chon, ho_ten=ten2, sdt=sdt2, email=mail2, so_du=sd2,
                    loai_kh=lk2, dia_phuong=dia2, diem_tin_dung=diem2, is_vip=vip2)
                st.rerun()
        xac_nhan = st.checkbox("Tôi chắc chắn muốn xóa " + ma_chon)
        if st.button("Xóa khách hàng", disabled=not xac_nhan):
            st.session_state.thong_bao = ql.xoa(ma_chon)
            st.rerun()

# ---------------- tab thống kê ----------------
with tab_tk:
    tong = sum(k["so_du"] for k in ql.ds)
    m1, m2, m3 = st.columns(3)
    m1.metric("Số khách hàng", len(ql))
    m2.metric("Tổng số dư", vnd(tong) + " đ")
    m3.metric("Số dư trung bình", vnd(tong / len(ql) if len(ql) else 0) + " đ")

    g1, g2 = st.columns(2)
    for cot, tieu_de, khung in (("loai_kh", "Theo loại khách hàng", g1),
                                ("dia_phuong", "Theo địa phương", g2)):
        tk = ql.thong_ke(cot)
        df = pd.DataFrame({"Nhóm": list(tk),
                           "Số lượng": [v["so_luong"] for v in tk.values()],
                           "Tổng số dư": [v["tong_so_du"] for v in tk.values()]})
        with khung:
            st.subheader(tieu_de)
            if len(df):
                st.bar_chart(df.set_index("Nhóm")["Số lượng"], color="#0b8a84")
            st.dataframe(df.sort_values("Số lượng", ascending=False), hide_index=True,
                         width="stretch",
                         column_config={"Tổng số dư": st.column_config.NumberColumn(format="%,.0f")})

# ---------------- tab Top-k ----------------
with tab_top:
    k = st.slider("Số khách hàng (k)", 1, 50, 10)
    top = ql.top_k_so_du(k)                  # heap
    df = bang(top)
    df.insert(0, "Hạng", range(1, len(df) + 1))
    st.dataframe(df, width="stretch", hide_index=True, column_config=CAU_HINH_SO_DU)
    if top:
        st.bar_chart(pd.DataFrame({"Số dư": [t["so_du"] for t in top]},
                                  index=["%02d. %s" % (i + 1, t["ho_ten"]) for i, t in enumerate(top)]),
                     color="#b8893b")

# ---------------- tab hàng đợi VIP ----------------
with tab_vip:
    st.caption("Khách được đánh dấu VIP hoặc có số dư từ 1 tỷ đồng trở lên tự động vào hàng đợi. "
               "Thứ tự ưu tiên: số dư lớn hơn trước, bằng nhau thì điểm tín dụng cao hơn trước, "
               "bằng cả hai thì vào hàng đợi trước được phục vụ trước (max-heap bằng heapq).")
    v1, v2 = st.columns(2)
    v1.metric("Số khách đang chờ", ql.so_luong_vip())
    v2.metric("Tổng khách hàng", len(ql))
    if st.button("Phục vụ khách tiếp theo", type="primary"):
        kh_vip = ql.phuc_vu_vip()
        if kh_vip is None:
            st.session_state.thong_bao = (False, "Hàng đợi VIP đang trống")
        else:
            st.session_state.thong_bao = (True, "Mời khách %s - %s (số dư %s đ, điểm tín dụng %d)" % (
                kh_vip["ma_kh"], kh_vip["ho_ten"], vnd(kh_vip["so_du"]), kh_vip["diem_tin_dung"]))
        st.rerun()
    so_xem = st.slider("Số khách hiển thị (đầu hàng đợi)", 1, 50, 10, key="so_xem_vip")
    dau_hang = ql.xem_hang_doi_vip(so_xem)
    df_vip = bang(dau_hang)
    df_vip.insert(0, "Thứ tự", range(1, len(df_vip) + 1))
    st.dataframe(df_vip, width="stretch", hide_index=True, column_config=CAU_HINH_SO_DU)
    st.caption("Hàng đợi chỉ tính các hồ sơ đang có trong danh sách. Phục vụ xong khách không bị xóa khỏi hệ thống; "
               "khi sửa hoặc hoàn tác hồ sơ đó, khách sẽ được xếp lại vào hàng đợi.")

# ---------------- tab CSV ----------------
with tab_csv:
    st.subheader("Xuất CSV")
    buf = io.StringIO()
    w = csv.DictWriter(buf, fieldnames=ql.TRUONG)
    w.writeheader()
    for kh in ql.ds:
        w.writerow({**kh, "ngay_dk": str(kh["ngay_dk"])})
    st.download_button("Tải khach_hang.csv", buf.getvalue().encode("utf-8-sig"),
                       "khach_hang.csv", "text/csv")
    st.subheader("Nhập CSV")
    f = st.file_uploader("Chọn file CSV (cùng định dạng file xuất)", type="csv")
    if f is not None and st.button("Nhập dữ liệu"):
        tam = "_tam_nhap.csv"
        with open(tam, "wb") as out:
            out.write(f.getvalue())
        st.session_state.kq_nhap = ql.doc_csv(tam)
        st.rerun()
    if st.session_state.get("kq_nhap"):
        so_them, loi = st.session_state.kq_nhap
        st.success("Đã thêm %d khách hàng, %d dòng lỗi" % (so_them, len(loi)))
        if loi:
            st.dataframe(pd.DataFrame(loi, columns=["Dòng", "Lý do"]), hide_index=True)

# ---------------- tab so sánh giải thuật ----------------
with tab_ss:
    st.caption("Chạy trực tiếp các giải thuật tự cài trên dữ liệu đang có và so sánh thời gian.")

    st.subheader("1. Tra cứu theo mã: Linear Search, Binary Search, Dictionary")
    ma_tim = st.text_input("Mã cần tra", value="KH000500", key="ma_ss").strip().upper()
    if st.button("Tra cứu bằng 3 cách"):
        t0 = time.perf_counter()
        da_sap = sorted(ql.ds, key=lambda k: k["ma_kh"])      # Binary Search cần danh sách đã sắp
        t_sap = time.perf_counter() - t0
        ket_qua = []
        for ten_pp, ham in (("Linear Search O(n)", lambda: tim_tuan_tu(ql.ds, ma_tim)),
                            ("Binary Search O(log n)", lambda: tim_nhi_phan(da_sap, ma_tim)),
                            ("Dictionary O(1)", lambda: ql.tra_cuu(ma_tim))):
            t_lap = []
            for _ in range(200):               # lặp 200 lần cho đo được
                a = time.perf_counter()
                kh = ham()
                t_lap.append(time.perf_counter() - a)
            ket_qua.append({"Phương pháp": ten_pp,
                            "Kết quả": (kh["ho_ten"] if kh else "Không tìm thấy"),
                            "Thời gian TB (ms)": round(ms(statistics.mean(t_lap)), 5)})
        st.dataframe(pd.DataFrame(ket_qua), hide_index=True, width="stretch")
        st.caption("Binary Search còn tốn thêm %.4f ms để sắp xếp danh sách trước khi tìm." % ms(t_sap))

    st.divider()
    st.subheader("2. Sắp xếp theo số dư: Insertion Sort và Merge Sort")
    n_ss = st.slider("Số hồ sơ đem sắp xếp", 100, min(5000, max(len(ql), 100)), min(1000, max(len(ql), 100)),
                     step=100, key="n_sx")
    if st.button("So sánh sắp xếp"):
        mau_ds = ql.ds[:n_ss]
        khoa = lambda k: k["so_du"]
        bang_kq = []
        kq_sap = {}
        for ten_pp, ham in (("Insertion Sort O(n²)", lambda: sap_xep_chen(mau_ds, khoa)),
                            ("Merge Sort tự cài O(n log n)", lambda: sap_xep_tron(mau_ds, khoa)),
                            ("sorted() của Python", lambda: sorted(mau_ds, key=khoa))):
            a = time.perf_counter()
            kq_sap[ten_pp] = ham()
            bang_kq.append({"Giải thuật": ten_pp, "Thời gian (ms)": round(ms(time.perf_counter() - a), 3)})
        giong = len({tuple(k["ma_kh"] for k in v) for v in kq_sap.values()}) == 1
        st.dataframe(pd.DataFrame(bang_kq), hide_index=True, width="stretch")
        st.caption("Kết quả của cả 3 cách " + ("giống nhau." if giong else "KHÁC nhau (cần kiểm tra lại)."))

    st.divider()
    st.subheader("3. Phát hiện CCCD trùng: hai vòng lặp và set")
    n_tr = st.slider("Số hồ sơ kiểm tra", 100, min(5000, max(len(ql), 100)), min(1000, max(len(ql), 100)),
                     step=100, key="n_trung")
    gan_trung = st.checkbox("Cố tình gán trùng CCCD cho 3 hồ sơ (giống TC24)", value=True)
    if st.button("So sánh phát hiện trùng"):
        mau_ds = [dict(k) for k in ql.ds[:n_tr]]
        if gan_trung and len(mau_ds) > 3:
            mau_ds[len(mau_ds) // 2]["cccd"] = mau_ds[0]["cccd"]
            mau_ds[-1]["cccd"] = mau_ds[0]["cccd"]
        a = time.perf_counter()
        r1 = trung_hai_vong_lap(mau_ds)
        t1 = time.perf_counter() - a
        a = time.perf_counter()
        r2 = trung_bang_set(mau_ds)
        t2 = time.perf_counter() - a
        st.dataframe(pd.DataFrame([
            {"Cách làm": "Hai vòng lặp O(n²)", "Số cặp/bản ghi trùng": len(r1), "Thời gian (ms)": round(ms(t1), 3)},
            {"Cách làm": "Dùng set/dict O(n)", "Số cặp/bản ghi trùng": len(r2), "Thời gian (ms)": round(ms(t2), 3)},
        ]), hide_index=True, width="stretch")

# ---------------- tab kiểm thử ----------------
with tab_test:
    st.caption("28 ca kiểm thử TC01-TC28 giống notebook. Mỗi ca dùng dữ liệu riêng nên không ảnh hưởng đến danh sách đang quản lý.")
    if st.button("Chạy 28 ca kiểm thử", type="primary"):
        st.session_state.kq_test = chay_kiem_thu()
    kq_test = st.session_state.get("kq_test")
    if kq_test:
        so_dat = sum(1 for t in kq_test if t["dat"])
        (st.success if so_dat == len(kq_test) else st.error)("Kiểm thử: %d/%d ca đạt" % (so_dat, len(kq_test)))
        df = pd.DataFrame([{"Mã": t["ma"], "Kết quả": "Đạt" if t["dat"] else "Không đạt",
                            "Mô tả": t["mo_ta"], "Đầu vào": t["dau_vao"],
                            "Mong đợi": t["mong_doi"], "Thực tế": t["thuc_te"]} for t in kq_test])
        st.dataframe(df, hide_index=True, width="stretch", height=600)

# ---------------- tab hiệu năng ----------------
with tab_perf:
    st.caption("Đo như phần 4 của notebook. n = 10.000 chạy khá lâu (khoảng 1 phút) vì có Insertion Sort và hai vòng lặp O(n²).")
    chon_n = st.multiselect("Chọn quy mô n", [100, 1000, 10000], default=[100, 1000])
    if st.button("Chạy đo hiệu năng", type="primary", disabled=not chon_n):
        thanh = st.progress(0.0, text="Đang đo...")
        perf, bo_nho = chay_hieu_nang(sorted(chon_n),
                                      lambda p, n: thanh.progress(p, text="Đã đo xong n = %d" % n))
        thanh.empty()
        st.session_state.kq_perf = (perf, bo_nho, sorted(chon_n))
    if st.session_state.get("kq_perf"):
        perf, bo_nho, dsn = st.session_state.kq_perf
        for nhom, ten in TEN_NHOM.items():
            st.subheader(ten)
            hang = []
            for pp in perf[nhom][dsn[0]]:
                dong = {"Phương pháp": pp}
                for n in dsn:
                    tb, lech = perf[nhom][n][pp]
                    dong["n=" + format(n, ",")] = "%.4f ± %.4f" % (ms(tb), ms(lech))
                hang.append(dong)
            st.dataframe(pd.DataFrame(hang), hide_index=True, width="stretch")
            st.caption("Đơn vị: ms, trung bình ± độ lệch chuẩn")
            if len(dsn) > 1:
                fig, ax = plt.subplots(figsize=(7, 3.2))
                for pp in perf[nhom][dsn[0]]:
                    ax.plot(dsn, [ms(perf[nhom][n][pp][0]) for n in dsn], marker="o", label=pp)
                ax.set_xscale("log")
                ax.set_yscale("log")
                ax.set_xlabel("Số bản ghi (n)")
                ax.set_ylabel("Thời gian TB (ms, log)")
                ax.grid(True, which="both", alpha=0.3)
                ax.legend(fontsize=8)
                st.pyplot(fig)
                plt.close(fig)
        st.subheader("Bộ nhớ và thời gian dựng chỉ mục")
        st.dataframe(pd.DataFrame([{"n": n, "Bộ nhớ (MB)": round(v["mb"], 2),
                                    "Dựng dict + set + Trie (s)": round(v["giay_nap"], 4)}
                                   for n, v in bo_nho.items()]), hide_index=True)
