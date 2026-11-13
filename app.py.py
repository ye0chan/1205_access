"""온가족 약상자 v2 | 무로그인 · 당뇨/고령자/관절 맞춤 확인 보조

배포: app.py + requirements.txt를 GitHub에 업로드 -> Streamlit Community Cloud,
main file app.py, Python 3.11 또는 3.12. 실행: streamlit run app.py
Secrets (모두 선택 사항; 미설정이면 수기 입력+내장 주의 규칙 사용):
MFDS_SERVICE_KEY = "공공데이터포털 Decoding 인증키"
GOOGLE_VISION_API_KEY = "Google Cloud Vision API key"
제품 허가정보/DUR 서비스 각각 활용승인 필요. 인증/로그인/계정 설정은 없음.
로직 검사: python app.py --self-test

데이터 경계: 가족 별칭/약 목록/건강 설정은 브라우저 서버 세션 메모리에만 유지.
다른 사용자의 세션과 공유하거나 전역 캐시에 저장하지 않음. DB/예약 푸시 없음.
이 브라우저 세션의 사용자는 모두 열람 가능. 공용 기기는 전체 세션 초기화 필요.
서버/프록시 로그·제3자 OCR 처리 정책까지 무기록을 보장하지 않음.
복용 체크는 사용자가 표시하는 기록일 뿐 알림/복약 확인 센서가 아님.

안전 경계: 규칙 기반 보조 시제품. 상용 의료 SW 인증/임상 검증 완료 제품 아님.
65세 이상 기준은 사용자가 확인한 연령군에만 적용. 할머니의 당뇨, 어머니의 관절
불편 외 나이/인슐린 사용/치매/신장질환은 추정하지 않음. 이 설정도 사용자가 수정.
국내 DUR 병용금기와 해외 라벨/지침 기반 주의를 다른 결과로 표시.
내장 규칙은 제한된 성분명 사전의 완전일치; 미매칭/부정확한 OCR은 누락 가능.
인슐린 종류/농도/제형/투여시각을 임의 교환/추정하지 않음. 용량 계산 없음.
음식 추천은 식재료 조합 예시이지 질환 치료식/검증된 영양소 계산이 아님.
신장 식이 제한/연하곤란/알레르기는 전문가 평가 우선.
상용 전: 국내 라벨/약사 검토, API 계약/전체 코드 매핑, 전향적 임상 검증,
사용성/접근성 검사, 개인정보/보안·규제 검토, 갱신/사고대응·감사 체계 필요.
내장 근거 확인일 2026-11-11. 이후 개정 자동 감지 없음; 자료별 연도는 화면 표시.
"""
from __future__ import annotations

import base64
import csv
import hashlib
import html
import io
import itertools
import json
import os
import re
import secrets
import sys
import time
import unicodedata
from datetime import datetime, timezone, timedelta
from urllib.parse import unquote

PRODUCT_SOURCE = "https://www.data.go.kr/data/15095677/openapi.do"
DUR_SOURCE = "https://www.data.go.kr/data/15059486/openapi.do"
PRODUCT_BASE = "https://apis.data.go.kr/1471000/DrugPrdtPrmsnInfoService08"
DUR_BASE = "https://apis.data.go.kr/1471000/DURPrdlstInfoService03"
SCHEMA_VERSION = 1


def now():
    return datetime.now(timezone(timedelta(hours=9))).isoformat(timespec="seconds")


def clean(value):
    return re.sub(r"\s+", " ", html.unescape(re.sub(r"<[^>]+>", " ", str(value or "")))).strip()


def norm(value):
    # No substring matching, transliteration, salt removal or fuzzy clinical equivalence.
    return re.sub(r"\s+", "", unicodedata.normalize("NFKC", str(value))).casefold()


def names(text):
    # One ingredient per line. Keep qualifiers/salt forms; do not split on commas.
    return list(dict.fromkeys(x.strip() for x in str(text).splitlines() if x.strip()))


def ingredient_suggestions(raw):
    # Only explicitly labelled fields; never treat all excipients as active ingredients.
    found = re.findall(r"성분명\s*[:：]\s*([^;|]+)", str(raw))
    return names("\n".join(clean(x) for x in found))


def duplicates(drugs):
    index = {}
    for drug in drugs:
        if not drug.get("confirmed"):
            continue
        for ingredient in drug.get("ingredients", []):
            key = norm(ingredient)
            if key:
                index.setdefault(key, {"ingredient": ingredient, "products": {}})["products"][drug["uid"]] = drug["name"]
    return [{"ingredient": v["ingredient"], "products": list(v["products"].values()),
             "uids": list(v["products"])} for v in index.values() if len(v["products"]) > 1]


def metric(rows):
    if not rows:
        raise ValueError("검증 행이 없습니다.")
    tp = fp = fn = tn = 0
    for row in rows:
        truth = str(row["expected_duplicate"]).strip()
        if truth not in {"0", "1"}:
            raise ValueError("expected_duplicate는 0 또는 1이어야 합니다.")
        a, b = json.loads(row["ingredients_a"]), json.loads(row["ingredients_b"])
        if not all(isinstance(x, list) and all(isinstance(y, str) for y in x) for x in (a, b)):
            raise ValueError("ingredients_a/b는 문자열 JSON 배열이어야 합니다.")
        if not a or not b or any(not x.strip() for x in a + b):
            raise ValueError("검증용 성분 목록은 비어 있을 수 없습니다.")
        predicted = bool({norm(x) for x in a} & {norm(x) for x in b})
        expected = truth == "1"
        tp += int(predicted and expected)
        fp += int(predicted and not expected)
        fn += int(not predicted and expected)
        tn += int(not predicted and not expected)
    precision = tp / (tp + fp) if tp + fp else None
    recall = tp / (tp + fn) if tp + fn else None
    f1 = 2 * tp / (2 * tp + fp + fn) if 2 * tp + fp + fn else None
    return dict(n=len(rows), TP=tp, FP=fp, FN=fn, TN=tn, precision=precision, recall=recall, F1=f1)


def self_test():
    def d(uid, ingredients, confirmed=True):
        return dict(uid=uid, name=uid, ingredients=ingredients, confirmed=confirmed)
    assert len(duplicates([d("a", ["아세트아미노펜", "카페인"]), d("b", [" 아세트아미노펜 "])])) == 1
    assert not duplicates([d("a", ["이부프로펜"]), d("b", ["덱시부프로펜"])])
    assert not duplicates([d("a", ["성분A"]), d("b", ["성분A"], False)])
    assert not duplicates([d("a", ["성분A", "성분A"])])
    assert not duplicates([d("a", ["성분A염산염"]), d("b", ["성분A"])])
    rows = [dict(ingredients_a='["A"]', ingredients_b='["A"]', expected_duplicate="1"),
            dict(ingredients_a='["A"]', ingredients_b='["B"]', expected_duplicate="0"),
            dict(ingredients_a='["C"]', ingredients_b='["C"]', expected_duplicate="0"),
            dict(ingredients_a='["D"]', ingredients_b='["E"]', expected_duplicate="1")]
    r = metric(rows)
    assert (r["TP"], r["FP"], r["FN"], r["TN"]) == (1, 1, 1, 1)
    assert r["precision"] == r["recall"] == r["F1"] == 0.5
    assert ingredient_suggestions("성분명 : 가상A; 분량 : 5; 성분명 : 가상B; 분량 : 2") == ["가상A", "가상B"]
    print("PASS: duplication, composite ingredients, unknown, salts, precision/recall/F1. Synthetic tests only.")


if __name__ == "__main__" and "--self-test" in sys.argv:
    self_test()
    sys.exit(0)

import requests
import streamlit as st
from PIL import Image, ImageOps

st.set_page_config(page_title="온가족 약상자 · 당뇨와 관절 맞춤", page_icon="💊", layout="centered", initial_sidebar_state="collapsed")


def setting(key, default=""):
    try:
        return st.secrets.get(key, os.environ.get(key, default))
    except Exception:
        return os.environ.get(key, default)


class ApiError(Exception):
    pass


def api_request(base, operation, params):
    key = str(setting("MFDS_SERVICE_KEY"))
    if not key:
        raise ApiError("공식 API 인증키 미설정 · 공식 조회 불가")
    # Do not include URL/exception details: these may contain the secret key.
    try:
        response = requests.get(f"{base}/{operation}", params={
            "serviceKey": unquote(key), "type": "json", **params}, timeout=(5, 18))
        response.raise_for_status()
        payload = response.json()
    except (requests.RequestException, ValueError):
        raise ApiError("공식 API 연결/응답 오류 · 키 권한, 트래픽 및 서비스 상태를 확인하세요.") from None
    root = payload.get("response", payload)
    header = root.get("header", {})
    if str(header.get("resultCode", "")) not in {"00", "0000", "0"}:
        raise ApiError("공식 API 오류 · 인증키/활용승인/호출 한도를 확인하세요.")
    body = root.get("body", {})
    items = body.get("items", [])
    if isinstance(items, dict):
        items = items.get("item", [])
    if items is None or items == "":
        items = []
    if isinstance(items, dict):
        items = [items]
    if not isinstance(items, list) or not all(isinstance(x, dict) for x in items):
        raise ApiError("예상과 다른 API 스키마 · 자동 판정을 중단합니다.")
    try:
        total = int(body["totalCount"])
    except (KeyError, TypeError, ValueError):
        raise ApiError("응답 건수 확인 불가 · 누락 여부를 판단할 수 없습니다.") from None
    return items, total


def search_products(query, barcode=False, page=1):
    params = {"pageNo": page, "numOfRows": 20}
    params["bar_code" if barcode else "item_name"] = query
    rows, total = api_request(PRODUCT_BASE, "getDrugPrdtPrmsnDtlInq08", params)
    if barcode:
        # Unknown barcode formatting is not accepted as a confirmed match.
        rows = [r for r in rows if query in re.findall(r"\d{8,14}", str(r.get("BAR_CODE", "")))]
    return rows, total


def get_dur(code):
    rows = []
    total = 0
    for page in range(1, 7):
        batch, total = api_request(DUR_BASE, "getUsjntTabooInfoList03", {
            "itemSeq": code, "pageNo": page, "numOfRows": 100})
        # A service ignoring itemSeq must never silently certify the query.
        if any(str(r.get("ITEM_SEQ", "")) != str(code) for r in batch):
            raise ApiError("DUR 품목코드 필터/응답이 일치하지 않습니다. 전문가 확인 필요.")
        rows.extend(batch)
        if len(rows) >= total:
            return {"rows": rows, "complete": True, "count": total, "checked_at": now()}
        if not batch:
            break
    return {"rows": rows, "complete": False, "count": total, "checked_at": now()}


def drug_from_row(row):
    raw = str(row.get("MATERIAL_NAME") or row.get("MAIN_ITEM_INGR") or "")
    code = str(row.get("ITEM_SEQ", ""))
    return dict(uid=secrets.token_hex(8), name=clean(row.get("ITEM_NAME")), code=code,
                company=clean(row.get("ENTP_NAME")), form=clean(row.get("FORM_CODE_NAME") or row.get("CHART")),
                strength="", raw=raw, ingredients=[], confirmed=False, kind="일반의약품",
                source=PRODUCT_SOURCE, updated=clean(row.get("CHANGE_DATE") or row.get("UPDATE_DATE") or "제공되지 않음"),
                retrieved=now(), warnings=clean(row.get("NB_DOC_DATA") or row.get("NB_DOC_ID")),
                demo=False, identification="공식 조회 · 사용자 확인 전")


def run_analysis(drugs):
    result = {"time": now(), "duplicate": duplicates(drugs), "contra": [], "notes": [],
              "coverage": [], "unconfirmed": [], "mechanisms": []}
    for d in drugs:
        if not d.get("confirmed") or not d.get("ingredients"):
            result["unconfirmed"].append(d["name"])
    all_demo = bool(drugs) and all(d.get("demo") for d in drugs)
    if all_demo:
        result["notes"].append("가상 예제: 공식 DUR 조회를 실행하지 않았습니다. 실제 복용 판단에 사용하지 마세요.")
        return result
    real = [d for d in drugs if d.get("code") and not d.get("demo") and d["kind"] != "건강기능식품"]
    for d in drugs:
        if d not in real:
            result["coverage"].append({"name": d["name"], "state": "공식 DUR 미조회 (코드 없음/건기식/가상)", "checked_at": "—"})
    targets = {str(d["code"]): d for d in real}
    seen = set()
    for d in real:
        try:
            data = get_dur(d["code"])
            state = f"조회 완료 · {data['count']}건 (이 앱 범위의 병용금기만)" if data["complete"] else "일부 조회 · 누락 가능"
            result["coverage"].append({"name": d["name"], "state": state, "checked_at": data["checked_at"]})
            for row in data["rows"]:
                other_code = str(row.get("MIXTURE_ITEM_SEQ", ""))
                if not other_code:
                    result["notes"].append(f"{d['name']}: 상대 품목코드 없는 DUR 행은 자동 매칭에서 제외했습니다.")
                    continue
                other = targets.get(other_code)
                if not other or other["uid"] == d["uid"]:
                    continue
                pair = tuple(sorted([d["uid"], other["uid"]]))
                if pair in seen:
                    continue
                seen.add(pair)
                reason = clean(row.get("PROHBT_CONTENT") or row.get("REMARK") or "사유 원문 미제공 · 약사에게 공식 자료 확인 요청")
                result["contra"].append({"products": [d["name"], other["name"]], "uids": list(pair),
                                         "reason": reason, "source": DUR_SOURCE,
                                         "notice_date": clean(row.get("NOTIFICATION_DATE")), "retrieved": data["checked_at"]})
                # Evidence extract only. No inference of enzyme, transporter or ADME pathway.
                sentences = re.split(r"(?<=[.!?。])\s+|\n", reason)
                excerpts = [s for s in sentences if re.search(r"CYP|P-gp|P glycoprotein|수송체|흡수|분포|대사|배설|청소율", s, re.I)]
                if excerpts:
                    result["mechanisms"].append({"products": [d["name"], other["name"]], "quote": " ".join(excerpts), "source": DUR_SOURCE})
        except ApiError as exc:
            result["coverage"].append({"name": d["name"], "state": f"조회 불가 · {exc}", "checked_at": now()})
    result["notes"].append("병용금기 미검출은 상호작용 없음이 아닙니다. 용량·투여경로·기간·질환·임신·연령·건기식·효능군 중복은 약사 확인이 필요합니다.")
    return result


def analysis_signature(member):
    return hashlib.sha256(json.dumps({"member": member, "profile": st.session_state.profiles.get(st.session_state.active, {})}, sort_keys=True, ensure_ascii=False).encode()).hexdigest()


def clear_analysis():
    st.session_state.pop("result", None)
    st.session_state.pop("result_signature", None)


def persist_add(drug, target):
    member = st.session_state.family[st.session_state.active]
    if sum(len(x) for x in member.values()) >= 12:
        st.error("구성원별 최대 12개입니다. 누락 약이 있으면 상담 시 별도로 전달하세요.")
        return False
    if drug.get("code") and any(d.get("code") == drug["code"] for group in member.values() for d in group):
        st.error("이미 등록한 품목입니다. 기존 항목을 확인하세요.")
        return False
    member[target].append(drug)
    clear_analysis()
    return True


def get_member():
    return st.session_state.family[st.session_state.active]


def public_snapshot():
    return {"schema": SCHEMA_VERSION, "created": now(), "family": st.session_state.family, "active": st.session_state.active}


def encrypt_backup(password):
    from cryptography.fernet import Fernet
    salt = secrets.token_bytes(16)
    key = base64.urlsafe_b64encode(hashlib.pbkdf2_hmac("sha256", password.encode(), salt, 390000, 32))
    return b"YAKCHECK1\n" + salt + Fernet(key).encrypt(json.dumps(public_snapshot(), ensure_ascii=False).encode())


def decrypt_backup(blob, password):
    from cryptography.fernet import Fernet
    prefix = b"YAKCHECK1\n"
    if not blob.startswith(prefix) or len(blob) > 2_000_000:
        raise ValueError("지원하지 않는 백업입니다.")
    salt, cipher = blob[len(prefix):len(prefix) + 16], blob[len(prefix) + 16:]
    key = base64.urlsafe_b64encode(hashlib.pbkdf2_hmac("sha256", password.encode(), salt, 390000, 32))
    data = json.loads(Fernet(key).decrypt(cipher, ttl=None))
    if data.get("schema") != 1 or not isinstance(data.get("family"), dict) or not 1 <= len(data["family"]) <= 8:
        raise ValueError("백업 스키마 오류")
    family = data["family"]
    for alias, groups in family.items():
        if not isinstance(alias, str) or not 1 <= len(alias) <= 20 or set(groups) != {"current", "planned"}:
            raise ValueError("구성원 형식 오류")
        if not all(isinstance(v, list) for v in groups.values()) or sum(map(len, groups.values())) > 12:
            raise ValueError("복약 목록 형식 오류")
        for drug in groups["current"] + groups["planned"]:
            if not isinstance(drug, dict) or not all(k in drug for k in ("uid", "name", "ingredients", "kind", "code")):
                raise ValueError("약 정보 형식 오류")
            if not all(isinstance(drug[k], str) for k in ("uid", "name", "kind", "code")):
                raise ValueError("약 정보 타입 오류")
            if not isinstance(drug["ingredients"], list) or not all(isinstance(x, str) for x in drug["ingredients"]):
                raise ValueError("성분 형식 오류")
            # Imported identification/confirmation cannot be blindly trusted.
            drug["confirmed"] = False
            drug["identification"] = "백업 복원 · 재확인 필요"
    return family


def report_lines(alias, member, result):
    lines = [f"약체크 | 약사 상담 카드 — {alias}", f"작성: {now()}", "진단·처방·복용 허가가 아닌 확인 보조 자료입니다."]
    for group, title in (("current", "복용 중"), ("planned", "구매 예정")):
        lines += [f"[{title}]"]
        if not member[group]:
            lines.append("등록 없음 (미입력 약 여부 확인 필요)")
        for d in member[group]:
            lines += [f"• {d['name']} / {d['kind']} / 품목코드: {d.get('code') or '없음'}",
                      f"  제형: {d.get('form') or '미확인'} | 함량: {d.get('strength') or '미확인'}",
                      f"  경로: {d.get('route', '미확인')} | 지시: {d.get('plan') or '미입력'} | 인슐린 메모: {d.get('insulin_note') or '미입력/해당 없음'}",
                      f"  성분: {', '.join(d.get('ingredients', [])) or '미확인'} | 사용자 확인: {'완료' if d.get('confirmed') else '필요'}",
                      f"  출처: {d.get('source') or '사용자 입력'} | 갱신: {d.get('updated', '미제공')} | 조회: {d.get('retrieved', '없음')}"]
    if not result:
        lines.append("검사 미실행: 공식 상호작용을 확인하지 않았습니다.")
    else:
        lines += [f"[확인 결과: {result['time']}]"]
        for x in result["duplicate"]:
            lines.append(f"중복 성분: {x['ingredient']} / {' + '.join(x['products'])} (명칭 정확일치; 용량 미평가)")
        for x in result["contra"]:
            lines += [f"공식 병용금기: {' + '.join(x['products'])}", f"근거: {x['reason']}", f"출처: {x['source']} / 조회: {x['retrieved']}"]
        for x in result["coverage"]:
            lines.append(f"조회 범위: {x['name']} / {x['state']} / {x['checked_at']}")
        for x in result["mechanisms"]:
            lines += [f"공식 기전 원문 발췌: {x['quote']}", f"출처: {x['source']}"]
        if not result["mechanisms"]:
            lines.append("ADME/CYP/수송체 기전: 확인한 공식 원문에서 제공되지 않음. 추정하지 않음.")
        if result["unconfirmed"]:
            lines.append("성분 미확인: " + ", ".join(result["unconfirmed"]))
        lines += result["notes"]
    profile = st.session_state.profiles.get(alias, {})
    lines += ["[건강 프로필 · 사용자 입력]", json.dumps(profile, ensure_ascii=False)]
    for warning in clinical_flags(member["current"] + member["planned"], profile):
        lines += [f"[{warning['level']}] {warning['title']}", warning['text'], "근거: " + warning['source']]
    lines += ["[약사에게 확인할 내용]", "1. 모든 처방약·일반약·건기식·필요시 복용약이 포함되었나요?",
              "2. 성분·함량·제형과 투여경로가 정확한가요?", "3. 질환·알레르기·임신/수유·연령·복용량·기간에 추가 주의가 있나요?",
              "임의로 복용을 중단하거나 용량을 변경하지 말고 약사·의사에게 문의하세요.",
              "정보 미검출/미조회는 안전하다는 뜻이 아닙니다.", f"제품 출처: {PRODUCT_SOURCE}", f"DUR 출처: {DUR_SOURCE}"]
    return lines


@st.cache_resource(show_spinner=False)
def pdf_font():
    from reportlab.pdfbase import pdfmetrics
    from reportlab.pdfbase.ttfonts import TTFont
    # Public font only. No patient information sent. Font licensed under OFL.
    url = "https://raw.githubusercontent.com/google/fonts/main/ofl/nanumgothic/NanumGothic-Regular.ttf"
    try:
        r = requests.get(url, timeout=(4, 12))
        r.raise_for_status()
        pdfmetrics.registerFont(TTFont("YakKorean", io.BytesIO(r.content)))
        return "YakKorean", True
    except Exception:
        from reportlab.pdfbase.cidfonts import UnicodeCIDFont
        pdfmetrics.registerFont(UnicodeCIDFont("HYSMyeongJo-Medium"))
        return "HYSMyeongJo-Medium", False


def make_pdf(lines):
    from reportlab.lib import colors
    from reportlab.lib.styles import ParagraphStyle
    from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer
    font, embedded = pdf_font()
    output = io.BytesIO()
    doc = SimpleDocTemplate(output, pagesize=(420, 595), rightMargin=24, leftMargin=24,
                            topMargin=25, bottomMargin=25, title="약사 상담 카드", author="약체크")
    style = ParagraphStyle("body", fontName=font, fontSize=9, leading=14,
                           textColor=colors.HexColor("#172B3A"), wordWrap="CJK", spaceAfter=5)
    story = []
    for i, line in enumerate(lines):
        heading = i == 0 or line.startswith("[")
        styled = ParagraphStyle(f"s{i}", parent=style, fontSize=12 if heading else 9,
                                leading=17 if heading else 14, spaceBefore=8 if heading else 0)
        story.append(Paragraph(html.escape(line), styled))
    if not embedded:
        story += [Spacer(1, 8), Paragraph("한글 대체 폰트 사용: PDF 뷰어에 따라 표시가 다를 수 있습니다.", style)]
    doc.build(story)
    return output.getvalue(), embedded


st.markdown("""<style>
:root{--ink:#172B3A;--teal:#087F8C;--paper:#F5F8FA}
[data-testid="stAppViewContainer"]{background:var(--paper)}
.block-container{max-width:560px;padding:1.1rem .85rem 1rem!important}
header[data-testid="stHeader"]{background:transparent;height:0}
h1,h2,h3,p{color:var(--ink)}
.hero{display:flex;gap:11px;align-items:center;margin:0 0 10px}
.logo{width:46px;height:46px;border-radius:16px;background:#D7F1ED;display:grid;place-items:center;font-size:27px}
.hero b{font-size:23px;letter-spacing:-1px}.hero small{display:block;font-size:12px;color:#526673}
.hint{font-size:11px;color:#536773;line-height:1.45;margin:7px 0}
.status{padding:10px 12px;border-radius:13px;background:#FFF1DE;color:#644214;font-size:13px;border:1px solid #EAC491}
[data-testid="stVerticalBlock"]{gap:.55rem}
.stButton>button,.stDownloadButton>button{border-radius:12px;min-height:42px}
[data-testid="stMetricValue"]{font-size:1.35rem}
[data-testid="stMetricLabel"]{font-size:.73rem}
[data-testid="stCaptionContainer"]{font-size:11px}
@media(max-width:600px){.block-container{padding-top:.6rem!important}.hero{margin-bottom:4px}.hero b{font-size:21px}
[data-testid="stHorizontalBlock"]{gap:.4rem;flex-wrap:nowrap!important}
[data-testid="stColumn"]{min-width:0!important;flex:1!important}
.stButton>button{font-size:12px;padding:.25rem .35rem} [data-testid="stMetricValue"]{font-size:1.1rem}}
/* Browser chrome, zoom, accessibility font sizes and long content vary.
   Never hide overflowing medical warnings to promise zero scrolling. */
</style>""", unsafe_allow_html=True)


# No login, account configuration or authentication dependencies.
editable = is_owner = True
is_demo = False
if "family" not in st.session_state:
    st.session_state.family = {k: {"current": [], "planned": []} for k in ("할머니", "어머니", "나")}
    st.session_state.active = "할머니"
if "profiles" not in st.session_state:
    st.session_state.profiles = {
        "할머니": dict(diabetes=True, age="미확인", cognition="미확인", kidney="미확인", joint="미확인", insulin="미확인", allergy=[], renal_diet=False),
        "어머니": dict(diabetes=False, age="미확인", cognition="미확인", kidney="미확인", joint="관절 불편 · 진단 미확인", insulin="미확인", allergy=[], renal_diet=False),
        "나": dict(diabetes=False, age="미확인", cognition="미확인", kidney="미확인", joint="미확인", insulin="미확인", allergy=[], renal_diet=False)}
for alias in st.session_state.family:
    st.session_state.profiles.setdefault(alias, dict(diabetes=False, age="미확인", cognition="미확인", kidney="미확인", joint="미확인", insulin="미확인", allergy=[], renal_diet=False))

@st.dialog("➕ 의약품 식별 · 등록", width="small")
def add_dialog():
    if not editable or is_demo:
        st.info("현재 목록에 약을 등록할 수 없습니다.")
        return
    target_label = st.segmented_control("등록 위치", ["💊 복용 중", "🛍️ 구매 예정"], default="🛍️ 구매 예정")
    target = "current" if target_label == "💊 복용 중" else "planned"
    method = st.segmented_control("검색 방법", ["🔎 제품명", "📷 사진", "▥ 바코드", "✍️ 직접"], default="🔎 제품명")
    if method in {"📷 사진", "▥ 바코드"}:
        st.caption("포장 사진만 사용하세요. 처방전·이름·주민번호 등 개인정보를 촬영하지 마세요. 사진은 목록에 저장하지 않습니다.")
        source = st.radio("이미지 입력", ["업로드", "촬영"], horizontal=True)
        upload = st.file_uploader("포장 이미지", type=["png", "jpg", "jpeg", "webp"]) if source == "업로드" else st.camera_input("포장 촬영")
        if upload:
            if upload.size > 8_000_000:
                st.error("8MB 이하 이미지를 사용하세요.")
                return
            if method == "▥ 바코드" and st.button("▥ 코드 읽기", use_container_width=True):
                try:
                    import zxingcpp
                    image = ImageOps.exif_transpose(Image.open(upload))
                    if image.width * image.height > 24_000_000:
                        raise ValueError("이미지 해상도가 너무 큽니다.")
                    codes = zxingcpp.read_barcodes(image.convert("RGB"))
                    values = list(dict.fromkeys(x.text for x in codes if re.fullmatch(r"\d{8,14}", x.text)))
                    if not values:
                        st.warning("숫자형 의약품 코드를 인식하지 못했습니다. 아래에 직접 입력하세요.")
                    else:
                        st.session_state.barcode_values = values
                        st.session_state.query_barcode = values[0]
                except Exception:
                    st.error("바코드 인식 실패 · 선명한 이미지 또는 직접 입력을 사용하세요.")
            if method == "📷 사진":
                consent = st.checkbox("사진을 Google Cloud Vision에 전송하는 데 동의합니다. 원문은 이 세션에서만 표시됩니다.")
                if st.button("🔤 OCR 읽기", disabled=not consent, use_container_width=True):
                    key = str(setting("GOOGLE_VISION_API_KEY"))
                    if not key:
                        st.error("GOOGLE_VISION_API_KEY 미설정 · 제품명으로 검색하거나 직접 입력하세요.")
                    else:
                        try:
                            image = ImageOps.exif_transpose(Image.open(upload))
                            if image.width * image.height > 24_000_000:
                                raise ValueError("해상도 제한")
                            image.thumbnail((2000, 2000))
                            buffer = io.BytesIO()
                            image.convert("RGB").save(buffer, format="JPEG", quality=88)
                            response = requests.post("https://vision.googleapis.com/v1/images:annotate",
                                params={"key": key}, json={"requests": [{"image": {"content": base64.b64encode(buffer.getvalue()).decode()},
                                "features": [{"type": "DOCUMENT_TEXT_DETECTION"}], "imageContext": {"languageHints": ["ko", "en"]}}]}, timeout=(5, 25))
                            response.raise_for_status()
                            entry = response.json().get("responses", [{}])[0]
                            if entry.get("error"):
                                raise ValueError("OCR 서비스 오류")
                            st.session_state.ocr_text = entry.get("fullTextAnnotation", {}).get("text", "")[:12000]
                            st.session_state.ocr_source = upload.name
                        except Exception:
                            st.error("OCR 인식 실패 · 이미지, 서비스 키 및 권한을 확인하세요.")
                if st.session_state.get("ocr_text"):
                    st.text_area("OCR 원문 · 제품명/성분/함량을 직접 수정 후 확인", key="ocr_text", height=140)
                    st.info("OCR은 문자 인식 보조입니다. 성분·함량을 약 정보로 자동 확정하지 않습니다. 아래 제품명 검색 후 공식 제품을 선택하세요.")
                    ocr_lines = [x.strip() for x in st.session_state.ocr_text.splitlines() if x.strip()]
                    hints = re.findall(r"\d+(?:\.\d+)?\s*(?:mg|mcg|μg|µg|g|mL|ml|IU|밀리그램|마이크로그램|그램)(?:\s*/\s*(?:정|캡슐|포|mL|ml))?", st.session_state.ocr_text, re.I)
                    st.caption("자동 추출 함량 후보 (확정 아님): " + (" · ".join(dict.fromkeys(hints)) or "미검출"))
                    labelled = ingredient_suggestions(st.session_state.ocr_text)
                    st.caption("자동 추출 성분명 후보 (확정 아님): " + (" · ".join(labelled) or "성분명 라벨 미검출 · 원문에서 직접 확인"))
                    chosen_line = st.selectbox("제품명 후보 · 실제 제품명인 행을 선택 후 수정", ocr_lines or [""], key="ocr_product_hint")
                    if st.button("선택 행을 검색어로 사용"):
                        st.session_state.query_name = chosen_line[:100]
        if method == "▥ 바코드" and len(st.session_state.get("barcode_values", [])) > 1:
            code = st.selectbox("인식된 코드 선택", st.session_state.barcode_values)
            if st.button("이 코드 사용"):
                st.session_state.query_barcode = code
                st.caption("선택한 코드를 아래 검색어에 반영했습니다.")
    manual = method == "✍️ 직접"
    if not manual:
        barcode = method == "▥ 바코드"
        query = st.text_input("바코드 숫자 (GTIN/표준코드)" if barcode else "제품명 · OCR 원문에서 정확히 옮겨 검색",
                              key="query_barcode" if barcode else "query_name", max_chars=100)
        search_page = st.number_input("결과 페이지", min_value=1, max_value=100, value=1, step=1)
        if st.button("🔎 공식 제품 검색", use_container_width=True):
            if not query.strip() or (barcode and not re.fullmatch(r"\d{8,14}", query.strip())):
                st.error("제품명 또는 올바른 숫자 코드를 입력하세요.")
            else:
                try:
                    with st.spinner("공식 허가정보 조회 중…"):
                        rows, total = search_products(query.strip(), barcode, int(search_page))
                    st.session_state.search_rows = rows
                    st.session_state.search_total = total
                    st.session_state.search_context = (method, query.strip(), int(search_page))
                    st.session_state.pop("selected_candidate", None)
                except ApiError as exc:
                    st.session_state.search_rows = []
                    st.error(str(exc))
        context = (method, query.strip(), int(search_page))
        rows = st.session_state.get("search_rows", []) if st.session_state.get("search_context") == context else []
        if rows:
            st.caption(f"전체 검색 {st.session_state.get('search_total')}건 · 현재 표시 {len(rows)}건. 제형/함량/업체가 다른 제품을 구분하세요.")
            selected = st.selectbox("공식 제품 선택", range(len(rows)), format_func=lambda i:
                f"{rows[i].get('ITEM_NAME', '?')} | {rows[i].get('ENTP_NAME', '')} | {rows[i].get('ITEM_SEQ', '')}")
            candidate = drug_from_row(rows[selected])
            if not candidate["code"] or not candidate["name"]:
                st.error("품목 식별정보 누락 · 등록할 수 없습니다.")
                return
            st.caption(f"제공 제형/성상: {candidate['form'] or '미제공'}")
            st.text_area("공식 원료/주성분 원문 · 첨가제를 유효성분에 포함하지 마세요", value=candidate["raw"] or "미제공", disabled=True, height=110)
            edit_form(candidate, target, f"official_{candidate['code']}")
        elif st.session_state.get("search_context") == context:
            st.warning("일치하는 제품을 확인하지 못했습니다. 제품명/제형/함량을 바꾸어 검색하거나 약사에게 확인하세요.")
    else:
        st.warning("직접 입력은 공식 제품 식별이 아닙니다. DUR 조회가 불가능하며 전문가 확인이 필요합니다.")
        candidate = dict(uid=secrets.token_hex(8), name="", code="", company="", form="", strength="", raw="",
                         ingredients=[], confirmed=False, kind="일반의약품", source="사용자 수기 입력", updated="미확인",
                         retrieved=now(), warnings="", demo=False, identification="사용자 수기 입력 · 공식 식별 미확인")
        edit_form(candidate, target, "manual")


def edit_form(candidate, target, widget_id, existing=None):
    with st.form(f"edit_{widget_id}"):
        title = st.text_input("제품명", value=candidate["name"], max_chars=180)
        options = ["일반의약품", "처방의약품", "건강기능식품"]
        kind = st.selectbox("구분", options, index=options.index(candidate.get("kind", "일반의약품")))
        form = st.text_input("제형 · 예: 정제/시럽/서방정", value=candidate.get("form", ""), max_chars=180)
        strength = st.text_input("성분별 함량·단위 · 예: 성분A 10 mg/정", value=candidate.get("strength", ""), max_chars=500)
        routes = ["미확인", "먹는 약", "피하 주사", "바르는 약", "점안/점비", "기타"]
        route = st.selectbox("투여경로 · 먹는 진통제와 바르는 진통제를 구분", routes, index=routes.index(candidate.get("route")) if candidate.get("route") in routes else 0)
        plan = st.text_input("처방/약사 지시 메모 · 복용 시각·횟수·식사 관계", value=candidate.get("plan", ""), max_chars=500)
        insulin_note = st.text_input("인슐린이면 정확한 펜 이름·농도(U/mL)·처방 투여량(U) 기록", value=candidate.get("insulin_note", ""), max_chars=300, help="앱은 단위를 환산하거나 증감하지 않습니다. 예: 농도와 투여 단위를 혼동하지 않도록 처방 내용을 그대로 기록하세요.")
        ingredients = st.text_area("유효성분만 한 줄에 하나 · 함량은 위 칸에 입력", value="\n".join(candidate.get("ingredients") or ingredient_suggestions(candidate.get("raw", ""))), height=100)
        confirmed = st.checkbox("공식 원문 또는 실제 포장과 대조하여 제품·제형·함량·모든 유효성분을 확인했습니다.", value=False)
        submitted = st.form_submit_button("💾 확인 후 저장", use_container_width=True)
    if submitted:
        values = names(ingredients)
        if not title.strip() or not form.strip() or not strength.strip() or not values or not confirmed:
            st.error("제품명·제형·함량·유효성분을 입력하고 대조 확인해 주세요.")
            return
        if len(values) > 50 or len(ingredients) > 6000:
            st.error("입력량 제한을 초과했습니다.")
            return
        # Editing a code-linked product's identity would invalidate the code mapping.
        if candidate.get("code") and title.strip() != candidate["name"]:
            st.error("공식 제품명은 변경할 수 없습니다. 다른 품목을 검색하세요.")
            return
        candidate.update(name=title.strip(), kind=kind, form=form.strip(), strength=strength.strip(),
                         ingredients=values, route=route, plan=plan.strip(), insulin_note=insulin_note.strip(), confirmed=True, identification="사용자 대조 확인 (전문가 검증 아님)")
        if existing:
            group, uid = existing
            get_member()[group] = [candidate if d["uid"] == uid else d for d in get_member()[group]]
            clear_analysis()
            st.rerun()
        elif persist_add(candidate, target):
            st.rerun()


@st.dialog("👪 가족 · 복용 목록", width="small")
def family_dialog():
    st.caption("로그인 없이 이 브라우저 세션만 사용합니다. 실제 이름/생년월일은 입력하지 마세요.")
    if is_owner:
        alias = st.text_input("새 구성원 별칭", max_chars=20)
        if st.button("👤 구성원 추가", disabled=is_demo):
            if alias.strip() and alias.strip() not in st.session_state.family and len(st.session_state.family) < 8:
                st.session_state.family[alias.strip()] = {"current": [], "planned": []}
                st.session_state.active = alias.strip()
                clear_analysis()
                st.rerun()
            else:
                st.warning("중복되지 않는 별칭을 입력하세요. 최대 8명입니다.")
    member = get_member()
    for group, label in (("current", "💊 복용 중"), ("planned", "🛍️ 구매 예정")):
        st.markdown(f"**{label}**")
        if not member[group]:
            st.caption("등록 없음")
        for d in member[group][:]:
            with st.expander(f"{d['name']} · {d['kind']}"):
                st.write("성분: " + (", ".join(d.get("ingredients", [])) or "미확인"))
                st.caption(f"제형 {d.get('form') or '미확인'} / 함량 {d.get('strength') or '미확인'} / 코드 {d.get('code') or '없음'}")
                st.caption(f"출처 {d.get('source', '없음')} / 갱신 {d.get('updated', '미제공')} / 조회 {d.get('retrieved', '없음')}")
                if editable and not is_demo:
                    edit_form(dict(d), group, d["uid"], (group, d["uid"]))
                    confirm_delete = st.checkbox("이 약을 목록에서 삭제", key=f"delconfirm_{d['uid']}")
                    if st.button("🗑️ 삭제", key=f"del_{d['uid']}", disabled=not confirm_delete):
                        member[group] = [x for x in member[group] if x["uid"] != d["uid"]]
                        clear_analysis()
                        st.rerun()
    if is_owner and len(st.session_state.family) > 1 and not is_demo:
        delete_family = st.checkbox("현재 구성원과 복용 목록 전체 삭제에 동의")
        if st.button("현재 구성원 삭제", disabled=not delete_family):
            del st.session_state.family[st.session_state.active]
            st.session_state.active = next(iter(st.session_state.family))
            clear_analysis()
            st.rerun()
    with st.expander("🔐 암호화 백업 · 복원"):
        st.caption("약 목록만 백업합니다. 건강 프로필·식재료·복용 체크 기록은 포함되지 않습니다. 공유 저장소가 아닙니다. 백업을 전달받은 사람은 비밀번호가 있어야 복원할 수 있습니다. 복원 후 모든 약을 재확인해야 합니다.")
        pw = st.text_input("백업 비밀번호 · 12자 이상", type="password", max_chars=128)
        if st.button("암호화 백업 만들기", disabled=len(pw) < 12 or is_demo):
            st.session_state.backup_bytes = encrypt_backup(pw)
        if st.session_state.get("backup_bytes"):
            st.download_button("⬇️ 암호화 파일", st.session_state.backup_bytes, "yakcheck.yak", "application/octet-stream")
        upload = st.file_uploader("백업 복원", type=["yak"])
        replace_ok = st.checkbox("현재 세션의 전체 가족 목록을 덮어씁니다")
        if st.button("복원 실행", disabled=not (upload and replace_ok and pw and is_owner and not is_demo)):
            try:
                family = decrypt_backup(upload.getvalue(), pw)
                st.session_state.family = family
                st.session_state.active = next(iter(family))
                st.session_state.profiles = {alias: dict(diabetes=False, age="미확인", cognition="미확인", kidney="미확인", joint="미확인", insulin="미확인", allergy=[], renal_diet=False) for alias in family}
                clear_analysis()
                st.rerun()
            except Exception:
                st.error("복원 실패: 비밀번호/파일 형식을 확인하세요. 기존 목록은 유지됩니다.")


@st.dialog("🔍 근거 · 확인 범위", width="small")
def detail_dialog():
    result = st.session_state.get("result")
    if not result:
        st.info("먼저 확인 검사를 실행하세요.")
        return
    st.caption("복용 중끼리, 구매 예정끼리, 두 그룹 사이의 등록된 모든 조합을 검사합니다. 중복은 성분명 정확일치이며 임상적 동등성·용량은 평가하지 않습니다.")
    for x in result["contra"]:
        st.error("⛔ 공식 병용금기 · " + " + ".join(x["products"]))
        st.write(x["reason"])
        st.caption(f"공고일: {x.get('notice_date') or '미제공'} / 조회: {x['retrieved']}")
        st.link_button("공식 DUR 출처", x["source"])
    for x in result["duplicate"]:
        st.warning("⚠️ 동일 성분 · " + x["ingredient"])
        st.write(" + ".join(x["products"]))
        st.caption("등록된 확인 성분 기준입니다. 실제 복용량·제형에 따른 의미는 약사에게 확인하세요.")
    st.markdown("**🧬 ADME · CYP · 수송체**")
    if result["mechanisms"]:
        for x in result["mechanisms"]:
            st.write(" + ".join(x["products"]))
            st.info(x["quote"])
            st.caption("공식 DUR 원문 문장 발췌 · 기전 분류/추론/추가 생성 없음")
    else:
        st.caption("확인한 공식 원문에 기전 정보 없음 또는 미조회. AI로 보충하지 않습니다.")
    st.markdown("**👵 질환·고령자 맞춤 주의 (국내 병용금기와 별개)**")
    for w in clinical_flags(get_member()["current"] + get_member()["planned"], st.session_state.profiles[st.session_state.active]):
        st.warning(w["title"])
        st.write(w["text"])
        st.link_button(w["evidence"], w["source"], key="evidence_" + w["id"])
    st.markdown("**📡 품목별 조회 상태**")
    for x in result["coverage"]:
        st.write(f"• {x['name']}: {x['state']}")
        st.caption(x["checked_at"])
    if result["unconfirmed"]:
        st.warning("성분 재확인 필요: " + ", ".join(result["unconfirmed"]))
    for note in result["notes"]:
        st.info(note)
    st.warning("추가 복용 여부·중단·용량 변경은 약사/의사에게 문의하세요. 호흡곤란·의식저하 등 응급 증상은 119로 도움을 요청하세요.")


@st.dialog("📄 약사 상담 카드", width="small")
def report_dialog():
    st.caption("실제 이름을 넣지 않은 별칭 기반 자료입니다. 공유 전 민감정보를 확인하세요. PDF는 기기 내 저장 후 직접 전달합니다.")
    lines = report_lines(st.session_state.active, get_member(), st.session_state.get("result"))
    st.text_area("상담 요약 미리보기", "\n".join(lines), height=260, disabled=True)
    if st.button("📄 PDF 생성", use_container_width=True):
        try:
            with st.spinner("한글 PDF 생성 중…"):
                data, embedded = make_pdf(lines)
            st.session_state.pdf_bytes = data
            st.session_state.pdf_signature = hashlib.sha256("\n".join([lines[0]] + lines[2:]).encode()).hexdigest()
            if not embedded:
                st.warning("한글 대체 폰트로 생성했습니다. 다운로드 후 표시 상태를 확인하세요.")
        except Exception:
            st.error("PDF 생성 실패 · 아래 텍스트 요약을 사용할 수 있습니다.")
    signature = hashlib.sha256("\n".join([lines[0]] + lines[2:]).encode()).hexdigest()
    if st.session_state.get("pdf_bytes") and st.session_state.get("pdf_signature") == signature:
        st.download_button("⬇️ 상담 PDF", st.session_state.pdf_bytes, "yakcheck-consultation.pdf", "application/pdf", use_container_width=True)
    st.download_button("⬇️ 텍스트 요약", "\n".join(lines), "yakcheck-consultation.txt", "text/plain;charset=utf-8", use_container_width=True)


@st.dialog("⚙️ 출처 · 검증 · 도움말", width="small")
def help_dialog():
    st.markdown("**공식 데이터**")
    st.link_button("식약처 제품 허가정보", PRODUCT_SOURCE)
    st.link_button("식약처 DUR 품목정보", DUR_SOURCE)
    st.caption("품목별 원문 갱신일이 없으면 미제공으로 표시합니다. 조회 시각은 자료 개정일이 아닙니다. 공식 API 결과를 이 앱이 임상적으로 검증했다는 뜻은 아닙니다.")
    st.markdown("**등록과 확인**")
    st.write("① 제품명/사진/바코드 → ② 공식 제품 선택 → ③ 제형·함량·유효성분 대조 → ④ 복용 중/구매 예정 등록 → ⑤ 검사 → ⑥ 약사 상담")
    st.write("OCR은 사진의 제품명·성분·함량 문자 인식을 보조합니다. 구조화·성분 확정은 사용자 확인이 필요합니다. 염/수화물·한영 동의어는 자동 통합하지 않아 미탐지할 수 있습니다. 건기식은 공식 DUR 자동 판정 대상이 아닙니다.")
    st.caption("실사용 목록은 세션 한정입니다. 로그인과 접근 권한 기능은 없습니다. 같은 브라우저 세션을 사용하는 사람은 목록에 접근할 수 있습니다. 공용 기기에서는 사용 후 세션을 초기화하세요.")
    st.markdown("**📊 중복 탐지 정확도 평가**")
    st.write("식약처 원문을 대조한 제품쌍별 정답을 전문가가 작성한 뒤 업로드하세요. 성분 입력 정확도·동의어 미탐지까지 반영하려면 실제 앱 추출/확인 성분을 입력값으로 사용하세요. 이 평가는 중복 성분 로직만 대상으로 하며 DUR/OCR 임상 성능 지표가 아닙니다.")
    template = io.StringIO()
    writer = csv.DictWriter(template, fieldnames=["case_id", "product_code_a", "product_code_b", "source", "verified_date", "ingredients_a", "ingredients_b", "expected_duplicate"])
    writer.writeheader()
    # Template synthetic data intentionally not presented as official validation.
    writer.writerow(dict(case_id="synthetic-example", product_code_a="가상A", product_code_b="가상B", source="가상 예제·교체 필요", verified_date="", ingredients_a='["가상성분 α"]', ingredients_b='["가상성분 α", "가상성분 β"]', expected_duplicate="1"))
    st.download_button("검증 CSV 양식 (가상 행을 교체하세요)", template.getvalue().encode("utf-8-sig"), "validation-template.csv", "text/csv")
    uploaded = st.file_uploader("전문가 검증 CSV · UTF-8", type=["csv"])
    if uploaded and st.button("정밀도 · 재현율 · F1 계산"):
        try:
            if uploaded.size > 2_000_000:
                raise ValueError("CSV는 2MB 이하여야 합니다.")
            rows = list(csv.DictReader(io.StringIO(uploaded.getvalue().decode("utf-8-sig"))))
            if len(rows) > 10000:
                raise ValueError("최대 10,000행입니다.")
            if not rows or any(not all(str(r.get(k, "")).strip() for k in ("case_id", "product_code_a", "product_code_b", "source", "verified_date")) for r in rows):
                raise ValueError("제품코드·출처·검증일·case_id를 모든 행에 기록하세요.")
            if len({r["case_id"] for r in rows}) != len(rows):
                raise ValueError("중복 case_id가 있습니다.")
            r = metric(rows)
            st.json(r)
            st.caption("null은 분모 0으로 계산 불가입니다. 표본 대표성·누락·정답 품질을 별도로 검토하세요. 업로드 출처를 앱이 독립 검증하지는 않습니다.")
        except (ValueError, KeyError, UnicodeError, TypeError) as exc:
            st.error("평가 실패: " + str(exc))
    wipe = st.checkbox("모든 약·건강 설정을 삭제하는 데 동의합니다")
    if st.button("🗑️ 전체 세션 초기화", use_container_width=True, disabled=not wipe):
        for key in list(st.session_state):
            del st.session_state[key]
        st.rerun()



# Versioned, deliberately small dictionary: aliases are explicit, never substring matches.
EVIDENCE_DATE = "2026-11-11"
SOURCES = {
    "insulin": ("DailyMed insulin glargine · 2023-06 label", "https://dailymed.nlm.nih.gov/dailymed/fda/fdaDrugXsl.cfm?setid=406883ea-7f97-4eff-8d43-0bab004654f1"),
    "beers": ("AGS Beers Criteria 2023 · 65세 이상 미국 지침", "https://pmc.ncbi.nlm.nih.gov/articles/PMC12478568/"),
    "kidney": ("NIDDK · 신장 보호와 NSAIDs", "https://www.niddk.nih.gov/health-information/kidney-disease/keeping-kidneys-safe"),
    "meal": ("CDC · Diabetes Meal Planning 2024", "https://www.cdc.gov/diabetes/healthy-eating/diabetes-meal-planning.html"),
    "hypo": ("NIDDK · Low Blood Glucose", "https://www.niddk.nih.gov/health-information/diabetes/overview/preventing-problems/low-blood-glucose-hypoglycemia"),
    "warfarin_food": ("NHS · 항응고제와 식품", "https://www.nhs.uk/medicines/anticoagulants/considerations/"),
    "joint": ("NICE NG226 · 골관절염 치료", "https://www.nice.org.uk/guidance/ng226/chapter/Recommendations")}
ALIASES = {
    "glargine": ["인슐린글라진", "인슐린글라르긴", "insulin glargine", "인슐린글라진(유전자재조합)", "인슐린글라진(유전자재조합,대장균)"],
    "insulin": ["인슐린", "insulin", "인슐린아스파트", "insulin aspart", "인슐린리스프로", "insulin lispro", "인슐린데글루덱", "insulin degludec", "사람인슐린", "휴먼인슐린", "human insulin", "인슐린데터미르", "insulin detemir"],
    "beta": ["비소프롤롤", "비소프롤롤푸마르산염", "bisoprolol", "프로프라놀롤", "프로프라놀롤염산염", "propranolol", "카르베딜롤", "carvedilol", "메토프롤롤", "메토프롤롤타르타르산염", "metoprolol", "아테놀롤", "atenolol"],
    "tzd": ["피오글리타존", "피오글리타존염산염", "pioglitazone"],
    "nsaid": ["이부프로펜", "ibuprofen", "덱시부프로펜", "dexibuprofen", "나프록센", "naproxen", "나프록센나트륨", "디클로페낙", "디클로페낙나트륨", "diclofenac", "셀레콕시브", "celecoxib", "멜록시캄", "meloxicam"],
    "anticholinergic": ["디펜히드라민", "디펜히드라민염산염", "diphenhydramine", "독실아민", "독실아민숙신산염", "doxylamine", "클로르페니라민", "클로르페니라민말레산염", "chlorpheniramine", "히드록시진", "히드록시진염산염", "hydroxyzine", "디멘히드리네이트", "dimenhydrinate"],
    "warfarin": ["와르파린", "와르파린나트륨", "warfarin"],
    "su": ["글리메피리드", "glimepiride", "글리벤클라미드", "glibenclamide", "glyburide", "글리피지드", "glipizide", "글리클라지드", "gliclazide"]}


def clinical_flags(drugs, profile):
    matched = {k: [] for k in ALIASES}
    unknown = []
    for d in drugs:
        if not d.get("confirmed"):
            continue
        for ingredient in d.get("ingredients", []):
            found = False
            for k, aliases in ALIASES.items():
                if norm(ingredient) in {norm(a) for a in aliases}:
                    matched[k].append(d["name"])
                    found = True
            if not found:
                unknown.append(ingredient)
    flags = []
    def add(key, title, text, source, level="전문가 확인"):
        evidence, url = SOURCES[source]
        flags.append(dict(id=key, title=title, text=text, source=url, evidence=evidence, level=level))
    insulin = bool(matched["glargine"] or matched["insulin"] or profile.get("insulin") == "사용 중")
    if profile.get("diabetes"):
        add("diabetes_context", "🩸 당뇨: 약 이름보다 성분·식사·신장기능부터", "인슐린 사용 여부/종류/농도와 모든 당뇨약을 입력하세요. 나이·최근 신장기능·식사 거름 여부가 미확인이면 개인별 복용 허용을 판단할 수 없습니다. 단순히 설탕이 없다는 이유로 약을 선택하지 마세요.", "meal", "정보 확인")
    if insulin:
        add("insulin_context", "💉 인슐린: 식사 변화·저혈당 위험 확인", "식사량·시간·활동·병용약 변화는 혈당에 영향을 줍니다. 농도(U/mL)와 실제 투여 단위(U)를 구별하고 펜 이름/성분을 대조하세요. 앱은 용량 환산·증감·인슐린 교체를 제안하지 않습니다. 근거 라벨은 글라진이며 다른 인슐린은 해당 국내 허가사항 확인이 필요합니다.", "insulin")
    if matched["glargine"] and matched["beta"]:
        add("glargine_beta", "⚠️ 글라진 + 베타차단제: 저혈당 증상이 가려질 수 있음", "일부 저혈당 경고 증상이 약해지거나 나타나지 않을 수 있습니다. 등록 약: " + " / ".join(set(matched["beta"])) + ". 느낌만으로 판단하지 말고 처방받은 혈당 확인 계획을 검토하세요. 국내 병용금기 확정이 아니며 임의 중단하지 마세요.", "insulin")
    elif insulin and matched["beta"]:
        add("other_insulin_beta", "🔎 인슐린 + 베타차단제: 제품별 저혈당 경고 확인", "글라진 라벨에 저혈당 증상 감소가 기재되어 있습니다. 현재 인슐린 종류가 글라진으로 확인되지 않아 해당 제품 허가사항으로 약사 확인이 필요합니다.", "insulin")
    if matched["glargine"] and matched["tzd"]:
        add("glargine_tzd", "⚠️ 글라진 + 피오글리타존: 체액저류·심부전 주의", "인슐린과 TZD 병용 시 체액저류가 심부전을 유발하거나 악화시킬 수 있다는 라벨 경고입니다. 새 부종·갑작스러운 체중 증가·숨참은 신속히 의료진에게 알리세요. 심한 호흡곤란은 119. 앱이 국내 병용금기로 지정하는 것은 아닙니다.", "insulin")
    if matched["nsaid"]:
        add("nsaid", "🦴 소염진통제: 신장·위장관·중복 사용 확인", "확인 성분이 있는 약: " + " / ".join(set(matched["nsaid"])) + ". 탈수/저혈압에서는 급성 신손상 위험이 있습니다. 신장질환·고령·다른 진통제 복용 시 자가 추가 전에 약사에게 확인하세요. 먹는 약과 바르는 약의 위험은 같지 않으므로 투여경로를 확인해야 합니다.", "kidney")
    older = profile.get("age") == "65세 이상"
    cognitive = profile.get("cognition") == "진단/증상 있음"
    if matched["anticholinergic"] and (older or cognitive):
        add("anticholinergic", "🧠 1세대 항히스타민: 혼돈·낙상·인지기능 주의", "확인 약: " + " / ".join(set(matched["anticholinergic"])) + ". Beers 기준은 고령자에서 강한 항콜린성 약의 일반적인 회피를 권고합니다. 누적 노출과 인지 저하/치매의 연관성이지 개인의 치매 발생을 확정하는 뜻은 아닙니다. 감기약·멀미약·수면유도제 중복을 상담하세요. 예외와 투여경로는 전문가가 판단합니다.", "beers")
    if older and matched["su"]:
        add("su", "🩸 65세 이상: 설포닐우레아계 저혈당 위험 검토", "해당 당뇨약의 지속 저혈당 위험과 대체 가능성을 처방의에게 검토 요청하세요. 임의로 중단하지 마세요. 앱은 제형·용량별 위험 순위나 대체 처방을 산출하지 않습니다.", "beers")
    if len(set(matched["nsaid"])) >= 2:
        add("nsaid_multiple", "⚠️ 서로 다른 소염진통제가 함께 등록됨", "성분명이 달라도 같은 NSAID 계열일 수 있습니다. 먹는 약/바르는 약, 처방 기간과 실제 동시 사용 여부를 약사가 확인해야 합니다. 동일 계열 등록만으로 병용금기를 확정하지 않습니다.", "kidney")
    if matched["warfarin"] and matched["nsaid"]:
        add("warfarin_nsaid", "⚠️ 와르파린 + NSAID: 출혈 위험 상담", "투여경로와 실제 동시 복용 여부를 먼저 확인하세요. 특히 경구 NSAID 추가는 출혈 위험 검토가 필요합니다. 흑색변·토혈·실신 등은 즉시 의료진 도움을 요청하세요. 처방 항응고제는 임의로 중단하지 마세요.", "beers")
    if matched["warfarin"]:
        add("warfarin_food", "🥬 와르파린: 채소를 끊기보다 섭취량 변화 상담", "비타민 K 함유 식품을 갑자기 늘리거나 줄이지 말고 INR 관리 계획을 의료진에게 확인하세요. 아래 식재료 예시는 개인의 항응고 치료에 맞춘 식단이 아닙니다.", "warfarin_food")
    if profile.get("joint") != "미확인":
        add("joint_context", "🦵 관절: 진단 먼저, 약 선택은 상담 항목으로", "관절 불편만으로 골관절염을 확정하지 않습니다. 골관절염이라면 운동을 기본으로 하고 무릎 등에서 바르는 NSAID를 상담할 수 있지만, 개인에게 복용/사용 가능하다는 뜻은 아닙니다. 글루코사민을 관절 치료제로 일괄 추천하지 않습니다. 갑자기 붓고 뜨겁거나 발열/보행 불가가 있으면 진료가 우선입니다.", "joint", "상담 의제")
    if unknown:
        add("unmatched", "❔ 내장 질환 규칙이 평가하지 못한 성분 있음", "제한된 규칙 사전 미매칭: " + ", ".join(dict.fromkeys(unknown)) + ". 이는 안전/위험 판정이 아닙니다. 국내 DUR 조회와 모든 약에 대한 전문가 검토가 별도로 필요합니다.", "beers", "평가 범위 밖")
    return flags


@st.dialog("👵 건강 설정 · 추정하지 않는 프로필", width="small")
def profile_dialog():
    alias = st.session_state.active
    p = st.session_state.profiles[alias]
    st.caption(f"{alias} · 의료진이 확인한 사실만 입력하세요. 나이·인슐린·치매 여부는 자동 추정하지 않습니다.")
    def choice(label, key, options):
        return st.selectbox(label, options, index=options.index(p.get(key)) if p.get(key) in options else 0)
    with st.form("health_profile"):
        diabetes = st.checkbox("당뇨병 진단 있음", value=p.get("diabetes", False))
        age = choice("연령군 (실제 생년월일 수집 안 함)", "age", ["미확인", "65세 미만", "65세 이상"])
        insulin = choice("인슐린 사용 · 사용 중이면 정확한 성분을 약 목록에도 등록", "insulin", ["미확인", "사용 중", "사용 안 함"])
        cognition = choice("인지기능 저하·치매 진단/증상", "cognition", ["미확인", "진단/증상 있음", "보고된 사항 없음"])
        kidney = choice("신장질환", "kidney", ["미확인", "진단 있음", "보고된 사항 없음"])
        joint = choice("관절 상태", "joint", ["미확인", "관절 불편 · 진단 미확인", "골관절염 진단 있음", "기타 관절질환 진단 있음"])
        renal_diet = st.checkbox("의료진의 신장 식이/칼륨·인·수분 제한 있음", value=p.get("renal_diet", False))
        allergy = st.multiselect("알레르기 식재료 · 선택한 재료를 포함하는 요리는 제외", ["두부", "달걀", "고등어", "닭가슴살", "브로콜리", "당근", "양배추", "현미밥"], default=p.get("allergy", []))
        if st.form_submit_button("건강 설정 저장", use_container_width=True):
            st.session_state.profiles[alias] = dict(diabetes=diabetes, age=age, insulin=insulin, cognition=cognition, kidney=kidney, joint=joint, renal_diet=renal_diet, allergy=allergy)
            clear_analysis()
            st.rerun()


RECIPES = [
    dict(name="두부·브로콜리 따뜻한 한 접시", ingredients={"두부", "브로콜리", "현미밥"}, steps=["두부는 속까지 충분히 가열하고 먹기 편하게 자릅니다.", "브로콜리는 씹기 편하게 익히고, 소스는 별도로 소량 제공합니다.", "채소 1/2, 단백질 1/4, 밥 1/4의 접시 구성을 참고합니다."], note="두부와 밥 모두 식사 계획에 반영해야 합니다. 밥을 빼는 식사를 인슐린 용량과 무관하게 적용하지 마세요."),
    dict(name="닭가슴살·양배추 부드러운 덮밥", ingredients={"닭가슴살", "양배추", "현미밥"}, steps=["닭은 중심까지 충분히 익히고 잘게 찢습니다.", "양배추를 부드럽게 익혀 밥과 분리해 담습니다.", "설탕/물엿 양념은 추가하지 않고 간은 개별 식사 지침을 따릅니다."], note="덮밥이어도 밥의 양을 확인하세요. 식사 시간은 처방받은 인슐린 계획에 맞추세요."),
    dict(name="달걀·당근 찜과 밥", ingredients={"달걀", "당근", "현미밥"}, steps=["달걀을 풀고 잘게 다진 당근을 섞습니다.", "속까지 충분히 익히고 뜨겁지 않게 식혀 제공합니다.", "가능하면 별도 비전분 채소 반찬을 보충합니다."], note="연하곤란이 있으면 부드러운 음식이라고 삼킴 안전성이 보장되지 않습니다. 전문 평가를 받으세요."),
    dict(name="고등어·브로콜리 구이 한 접시", ingredients={"고등어", "브로콜리", "현미밥"}, steps=["고등어는 가시를 철저히 제거하고 속까지 익힙니다.", "브로콜리는 부드럽게 익혀 준비합니다.", "염장 생선 대신 무염 재료를 우선 고려하고 밥은 개인 식사 계획에 맞춥니다."], note="관절염 치료/연골 재생 효과를 주장하는 레시피가 아닙니다. 생선 알레르기가 있으면 제외합니다.")]


def recipe_matches(selected, allergies):
    selected, allergies = set(selected), set(allergies)
    eligible = [r for r in RECIPES if not r["ingredients"] & allergies]
    return sorted(eligible, key=lambda r: (-len(r["ingredients"] & selected), r["name"]))


@st.dialog("🥗 냉장고 재료 → 오늘의 한 접시", width="small")
def food_dialog():
    p = st.session_state.profiles[st.session_state.active]
    st.caption("치료식 처방이나 영양소 정량 계산이 아닌, 선택 재료 기반의 조리 아이디어입니다.")
    if p.get("renal_diet") or p.get("kidney") == "진단 있음":
        st.warning("신장질환/식이 제한이 설정되어 일반 레시피 추천을 보류합니다. 칼륨·인·단백질·수분 허용량을 담당 영양사에게 먼저 확인하세요.")
        return
    if p.get("kidney") == "미확인":
        st.info("신장기능 미확인: 아래 조리 아이디어는 개인 질환에 적합하다는 뜻이 아닙니다.")
    selected = st.multiselect("지금 있는 재료", ["두부", "달걀", "고등어", "닭가슴살", "브로콜리", "당근", "양배추", "현미밥"], key="pantry_" + st.session_state.active)
    allergies = p.get("allergy", [])
    st.caption("물·식용유 등 기본 조리 재료는 별도입니다. 알레르기 교차접촉/포장 원재료는 직접 확인하세요.")
    if not selected:
        st.info("재료를 고르면 가능한 요리와 추가로 필요한 재료를 구분합니다.")
        return
    shown = 0
    for r in recipe_matches(selected, allergies):
        available = r["ingredients"] & set(selected)
        if not available:
            continue
        missing = r["ingredients"] - set(selected)
        with st.expander(("✅ 바로 조리: " if not missing else "🛒 추가 재료 필요: ") + r["name"], expanded=shown == 0):
            st.write("사용 재료: " + ", ".join(sorted(r["ingredients"])))
            if missing:
                st.write("없는 재료: " + ", ".join(sorted(missing)))
            for i, step in enumerate(r["steps"], 1):
                st.write(f"{i}. {step}")
            st.info(r["note"])
        shown += 1
        if shown == 3:
            break
    if not shown:
        st.warning("선택 재료와 알레르기 조건에 맞는 예시가 없습니다.")
    if p.get("diabetes"):
        st.info("당뇨 식사: 규칙적인 식사와 탄수화물 양의 일관성을 의료진과 계획하세요. 접시법은 채소 1/2·단백질 1/4·탄수화물 식품 1/4입니다. 이는 개인별 필요 열량/탄수화물 처방을 대신하지 않습니다.")
    st.caption("특정 음식이 인슐린과 무조건 병용금기라는 식으로 표시하지 않습니다. 식사 누락·급격한 식단 변경·음주 여부는 약사/영양사 상담에 포함하세요.")
    st.link_button(SOURCES["meal"][0], SOURCES["meal"][1])


@st.dialog("🕒 오늘의 복용 기록 · 수동 체크", width="small")
def adherence_dialog():
    st.caption("처방 일정에 따른 복용 여부를 직접 체크하는 메모입니다. 예약 알림이 아니며, 체크하지 않았다고 누락 복용을 확정하지 않습니다. 놓친 약을 두 배로 복용하지 마세요.")
    today = now()[:10]
    member = get_member()
    if not member["current"]:
        st.info("복용 중인 약을 먼저 등록하세요.")
    for d in member["current"]:
        st.markdown("**" + d["name"] + "**")
        st.caption("처방/약사 지시 메모: " + (d.get("plan") or "미입력 · 처방에 없는 시간은 체크하지 마세요."))
        for slot in ("아침", "점심", "저녁", "취침 전"):
            st.checkbox(f"{slot} · 해당 처방 회차를 복용함", key=f"taken_{st.session_state.active}_{d['uid']}_{today}_{slot}")
    st.caption("필요시 복용·주사·다회 투여를 완전하게 표현하는 전자 투약기록은 아닙니다. 세션 종료 시 기록이 소실될 수 있습니다.")


@st.dialog("🩸 저혈당 · 응급 행동", width="small")
def emergency_dialog():
    st.error("의식저하·경련·삼키기 어려움: 즉시 119. 입으로 음식/음료를 주지 마세요. 처방받은 글루카곤이 있으면 교육받은 보호자가 지침에 따라 사용하세요.")
    st.write("의식이 명료하고 안전하게 삼킬 수 있으며 혈당이 70 mg/dL 미만이거나 개인 목표보다 낮을 때: 빠르게 흡수되는 포도당/탄수화물 15~20g을 섭취하고, 15분 후 재측정합니다. 계속 낮으면 반복하고 지속·재발하거나 상태가 나빠지면 의료진 도움을 받으세요. 개별 응급계획이 있으면 그 계획을 우선하세요.")
    st.caption("일상 당뇨 식단에서 줄이는 단 음료와 저혈당 응급 교정은 상황이 다릅니다. 고지방 간식은 빠른 교정 대체품으로 삼지 마세요. 앱은 혈당 측정기/응급 연락을 대체하지 않습니다.")
    st.link_button(SOURCES["hypo"][0], SOURCES["hypo"][1])


# Home: compact overview, long clinical content stays in dialogs; warnings never clipped.
st.markdown('<div class="hero"><div class="logo">🌿</div><div><b>온가족 약상자</b><small>당뇨 · 인지기능 · 관절, 사람마다 다른 약 확인</small></div></div>', unsafe_allow_html=True)
selected = st.segmented_control("누구의 건강을 확인할까요?", list(st.session_state.family), default=st.session_state.active, label_visibility="collapsed")
if selected and selected != st.session_state.active:
    st.session_state.active = selected
    clear_analysis()
    st.rerun()
profile = st.session_state.profiles[st.session_state.active]
st.caption("👵 " + st.session_state.active + " · " + ("당뇨 관리" if profile.get("diabetes") else "일반 건강") + " · " + profile.get("age", "미확인") + " / 로그인 없음 · 세션만 보관")
c1, c2, c3 = st.columns(3)
with c1:
    if st.button("👤 건강 설정", use_container_width=True): profile_dialog()
with c2:
    if st.button("➕ 약 등록", use_container_width=True): add_dialog()
with c3:
    if st.button("🥗 재료·요리", use_container_width=True): food_dialog()
member = get_member()
with st.container(height=130, border=True):
    for group, icon, label in (("current", "💊", "복용 중"), ("planned", "🛍️", "구매 예정")):
        st.markdown(f"**{icon} {label} {len(member[group])}**")
        st.caption(" · ".join(d["name"] + (" ⚠ 재확인" if not d.get("confirmed") else "") for d in member[group]) or "등록된 약 없음 · 실제 성분을 입력하세요")
all_drugs = member["current"] + member["planned"]
flags = clinical_flags(all_drugs, profile)
if st.button("🛡️ 이 가족의 약 · 질환 주의 확인", type="primary", use_container_width=True, disabled=not all_drugs):
    with st.spinner("공식 조회 및 질환별 주의 확인 중…"):
        st.session_state.result = run_analysis(all_drugs)
        st.session_state.result_signature = analysis_signature(member)
result = st.session_state.get("result")
if result and st.session_state.get("result_signature") != analysis_signature(member):
    clear_analysis()
    result = None
if result:
    a,b,c = st.columns(3)
    with a: st.metric("⚠️ 성분 중복",len(result["duplicate"]))
    with b: st.metric("⛔ 공식 금기",len(result["contra"]))
    with c: st.metric("👤 맞춤 확인",len(flags))
    if result["contra"]:
        st.error("공식 병용금기 확인 · 추가 복용 전 약사 확인")
    elif result["duplicate"]:
        st.warning("동일 성분 확인 · 실제 복용량과 병용 여부 상담")
    else:
        st.info("중복·공식 금기 미검출은 안전 판정이 아닙니다.")
    incomplete = sum(not x["state"].startswith("조회 완료") for x in result["coverage"])
    if incomplete: st.caption(f"📡 {incomplete}개 품목 공식 조회 불완전/불가 · 상세 근거에서 확인")
    if st.button("🔍 맞춤 경고 · 근거 · 미조회 범위", use_container_width=True): detail_dialog()
else:
    st.caption("① 건강 설정 → ② 복용·구매 예정 약 등록 → ③ 확인. 병명만으로 복용 가능/불가를 단정하지 않습니다.")
a,b,c = st.columns(3)
with a:
    if st.button("👪 약 목록", use_container_width=True): family_dialog()
with b:
    if st.button("🕒 복용 체크", use_container_width=True): adherence_dialog()
with c:
    if st.button("📄 상담 PDF", use_container_width=True): report_dialog()
a,b = st.columns(2)
with a:
    if st.button("🩸 저혈당 대처", use_container_width=True): emergency_dialog()
with b:
    if st.button("⚙️ 출처·검증", use_container_width=True): help_dialog()
st.caption("의학적 판단·용량 변경 기능이 아닙니다. 개인별 허가사항은 약사 확인이 필요합니다. 근거 확인: " + EVIDENCE_DATE)
