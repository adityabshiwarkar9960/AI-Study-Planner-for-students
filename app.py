"""
AI Study Planner & Productivity Coach
======================================
Main Flask application entry point.

Run with:  python app.py
Visit:     http://127.0.0.1:5000
"""

from flask import (Flask, render_template, request, redirect,
                   url_for, session, jsonify, flash, make_response,
                   send_from_directory)
import sqlite3
import os
import json
import io
import random
import re
import zipfile
import tempfile
from datetime import datetime, date, timedelta
from functools import wraps
from collections import defaultdict, Counter
from werkzeug.security import generate_password_hash, check_password_hash
import pandas as pd
from pypdf import PdfReader

from ai_engine.schedule_generator import generate_schedule, get_priority_breakdown
from utils.productivity_tracker import (
    calculate_productivity_score,
    get_weekly_stats,
    get_study_streak,
    get_motivational_message,
)
import socket
import webbrowser
import secrets
import smtplib
from email.message import EmailMessage
from werkzeug.utils import secure_filename


BASE_DIR = os.path.dirname(__file__)


def _is_hosted_runtime():
    """Return True when running on a hosted platform with ephemeral storage."""
    return any(
        os.environ.get(name)
        for name in ("RENDER", "RENDER_SERVICE_ID", "VERCEL", "VERCEL_ENV")
    )


def get_database_path():
    """Return a writable database path for the current environment."""
    override_path = os.environ.get("DATABASE_PATH")
    if override_path:
        return override_path
    if _is_hosted_runtime():
        return os.path.join(tempfile.gettempdir(), "ai_student_planner.db")
    return os.path.join(BASE_DIR, "database.db")


def get_upload_folder():
    """Return the avatar upload folder for the current environment."""
    override_path = os.environ.get("UPLOAD_FOLDER")
    if override_path:
        return override_path
    if _is_hosted_runtime():
        return os.path.join(tempfile.gettempdir(), "uploads", "avatars")
    return os.path.join(BASE_DIR, "static", "uploads", "avatars")


# Password reset tokens table creation
def ensure_password_resets_table():
    # Use direct sqlite connection here because get_db() may not be defined yet
    db_path = get_database_path()
    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    conn.execute("""
        CREATE TABLE IF NOT EXISTS password_resets (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            token TEXT NOT NULL UNIQUE,
            expires_at DATETIME NOT NULL,
            created_at DATETIME DEFAULT CURRENT_TIMESTAMP
        );
    """)
    conn.commit()
    conn.close()

ensure_password_resets_table()

# ── App configuration ────────────────────────────────────────────────────────
app = Flask(__name__)
app.secret_key = os.environ.get("SECRET_KEY", "study-planner-secret-key-2024")
DATABASE = get_database_path()
UPLOAD_FOLDER = get_upload_folder()
os.makedirs(UPLOAD_FOLDER, exist_ok=True)


# ── Database helpers ─────────────────────────────────────────────────────────
def get_db():
    """Open a database connection and enable row-factory mode."""
    conn = sqlite3.connect(DATABASE)
    conn.row_factory = sqlite3.Row
    return conn


def safe_get(row, key, default=None):
    """Safely get a value from a mapping-like or sqlite3.Row object.

    sqlite3.Row doesn't implement `.get()`, so try `.get()` first then fallback
    to index access. Returns `default` on any error.
    """
    if row is None:
        return default
    try:
        return row.get(key, default)
    except Exception:
        try:
            return row[key]
        except Exception:
            return default


QUIZ_MAX_QUESTIONS = 5
QUIZ_MIN_SENTENCE_WORDS = 8
QUIZ_MAX_SENTENCE_WORDS = 45
QUIZ_STOPWORDS = {
    "about", "after", "again", "also", "because", "been", "being", "between",
    "could", "doing", "during", "each", "from", "have", "having", "into", "most",
    "other", "over", "such", "than", "that", "their", "there", "these", "they",
    "this", "those", "through", "under", "very", "were", "what", "when", "where",
    "which", "while", "with", "would", "your", "student", "study", "subject",
    "chapter", "section", "page", "pages", "figure", "table", "example",
    "also", "can", "may", "might", "must", "should", "will", "shall", "using",
    "used", "use", "because", "however", "therefore", "thus", "then", "than",
    "into", "onto", "over", "under", "about", "across", "within", "without"
}

QUIZ_CUE_PATTERNS = [
    r"\b(is|are|was|were)\s+(?:the\s+)?(.{4,120}?)\s*(?:[.;,]|$)",
    r"\bmeans\s+(?:the\s+)?(.{4,120}?)\s*(?:[.;,]|$)",
    r"\brefers?\s+to\s+(?:the\s+)?(.{4,120}?)\s*(?:[.;,]|$)",
    r"\bdefined\s+as\s+(?:the\s+)?(.{4,120}?)\s*(?:[.;,]|$)",
    r"\bconsists?\s+of\s+(?:the\s+)?(.{4,120}?)\s*(?:[.;,]|$)",
    r"\bincludes?\s+(?:the\s+)?(.{4,120}?)\s*(?:[.;,]|$)",
    r"\brepresents?\s+(?:the\s+)?(.{4,120}?)\s*(?:[.;,]|$)",
    r"\bresults?\s+in\s+(?:the\s+)?(.{4,120}?)\s*(?:[.;,]|$)",
    r"\bleads?\s+to\s+(?:the\s+)?(.{4,120}?)\s*(?:[.;,]|$)",
]

QUIZ_GENERIC_CHOICES = [
    "concept", "method", "process", "principle", "factor", "system", "result", "effect",
    "feature", "property", "idea", "stage", "cause", "result", "example", "solution",
]

QUIZ_GENERIC_PHRASES = {
    "main idea",
    "important concepts",
    "important concept",
    "these tasks",
    "this pdf",
    "sample quiz pdf",
    "overview",
    "core concepts",
    "revision notes",
    "real-world applications",
    "use this pdf",
    "regular sentences",
    "multiple-choice questions",
    "the main idea",
}

QUIZ_GENERIC_WORDS = {
    "important", "concept", "concepts", "overview", "notes", "applications",
    "review", "sample", "question", "questions", "sentence", "sentences",
    "tasks", "idea", "ideas", "pdf",
}

QUIZ_BAD_ANSWER_WORDS = {
    "perform", "learns", "learn", "uses", "used", "using", "helps", "allows",
    "combines", "supports", "creates", "creating", "made", "make", "making",
    "field", "human", "normally", "requiring", "that", "these", "this", "those",
    "carry", "needs", "include", "includes", "contains", "contain", "produce",
    "produces", "real", "world", "tasks",
}

QUIZ_DEFINITION_CUES = (
    "is", "are", "was", "were", "means", "refers to", "defined as",
    "consists of", "includes", "represents", "results in", "leads to",
)


def _extract_pdf_text(uploaded_file) -> str:
    uploaded_file.stream.seek(0)
    reader = PdfReader(uploaded_file.stream)
    pages = []
    for page in reader.pages:
        pages.append(page.extract_text() or "")
    return "\n".join(pages).strip()


def _normalize_quiz_text(text: str) -> str:
    normalized = re.sub(r"\r\n?", "\n", text or "")
    normalized = re.sub(r"\n{2,}", ". ", normalized)
    normalized = re.sub(r"[\t ]+", " ", normalized)
    normalized = re.sub(r"\s*\n\s*", " ", normalized)
    return re.sub(r"\s+", " ", normalized).strip()


def _split_quiz_sentences(text: str):
    sentences = []
    for sentence in re.split(r"(?<=[.!?])\s+", text):
        cleaned = sentence.strip().strip("•-–—")
        word_count = len(cleaned.split())
        if QUIZ_MIN_SENTENCE_WORDS <= word_count <= QUIZ_MAX_SENTENCE_WORDS:
            sentences.append(cleaned)
    return sentences


def _looks_like_quiz_heading(line: str) -> bool:
    cleaned = re.sub(r"\s+", " ", line or "").strip()
    if not cleaned:
        return True
    if re.search(r"[.!?]$", cleaned):
        return False

    words = cleaned.split()
    word_count = len(words)
    if word_count > 10:
        return False

    if re.search(r"\b(is|are|was|were|means|refers?|defined|consists?|includes?|results?|leads?|helps|allows|supports|combines|uses|can|may|might|should)\b", cleaned, re.IGNORECASE):
        return False

    alpha_words = [word for word in words if re.search(r"[A-Za-z]", word)]
    if not alpha_words:
        return True

    title_like = sum(1 for word in alpha_words if word[:1].isupper()) / len(alpha_words) >= 0.6
    short_and_title_like = word_count <= 6 and title_like
    title_with_colon = word_count <= 8 and ":" in cleaned and title_like
    return short_and_title_like or title_with_colon


def _quiz_content_text(text: str) -> str:
    body_lines = []
    for raw_line in re.split(r"\r?\n", text or ""):
        line = re.sub(r"\s+", " ", raw_line).strip()
        if not line or _looks_like_quiz_heading(line):
            continue
        body_lines.append(line)
    return " ".join(body_lines)


def _clean_quiz_phrase(text: str) -> str:
    cleaned = re.sub(r"\s+", " ", text or "").strip(" \t\n\r.,;:!?()[]{}-")
    cleaned = re.sub(r"^(?:the|a|an)\s+", "", cleaned, flags=re.IGNORECASE)
    cleaned = re.sub(r"\b(?:and|or|of|to|in|for|with|on|at|by)\s*$", "", cleaned, flags=re.IGNORECASE)
    return cleaned.strip()


def _quiz_words(text: str):
    return [
        token.lower()
        for token in re.findall(r"[A-Za-z][A-Za-z\-']+", text or "")
        if len(token) >= 4 and token.lower() not in QUIZ_STOPWORDS
    ]


def _phrase_candidates_for_sentence(sentence: str):
    words = _quiz_words(sentence)
    candidates = []
    for size in (3, 2, 1):
        for index in range(0, len(words) - size + 1):
            candidate = " ".join(words[index:index + size]).strip()
            if len(candidate.split()) == 1 and candidate in QUIZ_STOPWORDS:
                continue
            candidates.append(candidate)
    return candidates


def _extract_definition_pair(sentence: str):
    patterns = [
        r"\b(?P<subject>.+?)\s+(?:is|are|was|were)\s+(?:the|a|an|one of the|part of the|type of|form of|kind of)?\s*(?P<predicate>[^.;:]{4,140}?)\s*(?:[.;,]|$)",
        r"\b(?P<subject>.+?)\s+means\s+(?:the|a|an)?\s*(?P<predicate>[^.;:]{4,140}?)\s*(?:[.;,]|$)",
        r"\b(?P<subject>.+?)\s+refers?\s+to\s+(?:the|a|an)?\s*(?P<predicate>[^.;:]{4,140}?)\s*(?:[.;,]|$)",
        r"\b(?P<subject>.+?)\s+defined\s+as\s+(?:the|a|an)?\s*(?P<predicate>[^.;:]{4,140}?)\s*(?:[.;,]|$)",
        r"\b(?P<subject>.+?)\s+consists?\s+of\s+(?:the|a|an)?\s*(?P<predicate>[^.;:]{4,140}?)\s*(?:[.;,]|$)",
        r"\b(?P<subject>.+?)\s+includes?\s+(?:the|a|an)?\s*(?P<predicate>[^.;:]{4,140}?)\s*(?:[.;,]|$)",
        r"\b(?P<subject>.+?)\s+represents?\s+(?:the|a|an)?\s*(?P<predicate>[^.;:]{4,140}?)\s*(?:[.;,]|$)",
        r"\b(?P<subject>.+?)\s+results?\s+in\s+(?:the|a|an)?\s*(?P<predicate>[^.;:]{4,140}?)\s*(?:[.;,]|$)",
        r"\b(?P<subject>.+?)\s+leads?\s+to\s+(?:the|a|an)?\s*(?P<predicate>[^.;:]{4,140}?)\s*(?:[.;,]|$)",
    ]

    for pattern in patterns:
        match = re.search(pattern, sentence, re.IGNORECASE)
        if not match:
            continue
        subject = _clean_quiz_phrase(re.split(r"[,;:]", match.group("subject"), maxsplit=1)[0])
        predicate = _clean_quiz_phrase(match.group("predicate"))
        if subject and predicate and _is_valid_quiz_answer(subject):
            return subject, predicate
    return None, None


def _find_original_phrase(sentence: str, phrase: str):
    if not phrase:
        return ""
    match = re.search(rf"\b{re.escape(phrase)}\b", sentence, re.IGNORECASE)
    return match.group(0).strip() if match else phrase


def _is_valid_quiz_answer(answer: str) -> bool:
    cleaned = _clean_quiz_phrase(answer).lower()
    if not cleaned:
        return False
    if cleaned in QUIZ_GENERIC_PHRASES:
        return False
    if cleaned.startswith(("this ", "that ", "these ", "those ", "important ", "use this ", "sample ")):
        return False

    words = cleaned.split()
    if len(words) == 1:
        return len(cleaned) >= 4 and cleaned not in QUIZ_GENERIC_WORDS and cleaned not in QUIZ_STOPWORDS
    if len(words) > 4:
        return False
    if any(word in QUIZ_BAD_ANSWER_WORDS for word in words):
        return False
    return True


def _is_meta_quiz_sentence(sentence: str) -> bool:
    lowered = re.sub(r"\s+", " ", sentence or "").strip().lower()
    if not lowered:
        return True
    return any(
        phrase in lowered
        for phrase in (
            "main idea",
            "important concepts",
            "use this pdf",
            "sample quiz pdf",
            "multiple-choice questions",
            "contains regular sentences",
            "regular sentences",
            "test the quiz generator",
        )
    )


def _extract_salient_phrase(sentence: str, phrase_frequency: Counter, token_frequency: Counter):
    best_phrase = None
    best_score = -1

    words = _quiz_words(sentence)
    if not words:
        return None

    for candidate in _phrase_candidates_for_sentence(sentence):
        if not _is_valid_quiz_answer(candidate):
            continue
        candidate_words = candidate.split()
        if not candidate_words:
            continue
        score = phrase_frequency.get(candidate, 0) * 3
        score += sum(token_frequency.get(word, 0) for word in candidate_words)
        score += len(candidate_words) * 2
        if score > best_score:
            best_phrase = candidate
            best_score = score

    if best_phrase:
        candidate = _find_original_phrase(sentence, best_phrase)
        candidate_words = candidate.split()
        if len(candidate_words) > 1:
            has_title_case = any(word[:1].isupper() or word.isupper() for word in candidate_words)
            if not has_title_case and phrase_frequency.get(best_phrase, 0) <= 1:
                best_phrase = None
            else:
                return candidate if _is_valid_quiz_answer(candidate) else None
        else:
            return candidate if _is_valid_quiz_answer(candidate) else None

    fallback_words = [word for word in words if word not in QUIZ_STOPWORDS]
    if not fallback_words:
        return None
    fallback_words.sort(key=lambda word: (token_frequency.get(word, 0), len(word)), reverse=True)
    candidate = _find_original_phrase(sentence, fallback_words[0])
    return candidate if _is_valid_quiz_answer(candidate) else None


def _sentence_score(sentence: str) -> int:
    score = len(sentence.split())
    if re.search(r"\b(is|are|was|were|means|refers?|defined|consists?|includes?|results?|leads?|represents?)\b", sentence, re.IGNORECASE):
        score += 10
    if re.search(r"\b(?:important|important|main|key|primary|central|significant|because|therefore)\b", sentence, re.IGNORECASE):
        score += 4
    return score


def _extract_answer_phrase(sentence: str, term_frequency: Counter) -> str | None:
    best_phrase = None
    best_score = -1

    for pattern in QUIZ_CUE_PATTERNS:
        for match in re.finditer(pattern, sentence, re.IGNORECASE):
            phrase_group = match.group(2) if match.lastindex and match.lastindex >= 2 else match.group(1)
            if not phrase_group:
                continue
            phrase = _clean_quiz_phrase(phrase_group)
            words = phrase.split()
            if not (2 <= len(words) <= 12):
                continue
            phrase_score = sum(term_frequency.get(word.lower(), 0) for word in words)
            phrase_score += len(words)
            if phrase_score > best_score:
                best_phrase = phrase
                best_score = phrase_score

    if best_phrase:
        return best_phrase

    tokens = [
        token for token in re.findall(r"[A-Za-z][A-Za-z\-']+", sentence)
        if len(token) >= 5 and token.lower() not in QUIZ_STOPWORDS
    ]
    if not tokens:
        return None

    tokens.sort(key=lambda token: (term_frequency.get(token.lower(), 0), len(token)), reverse=True)
    fallback = _clean_quiz_phrase(tokens[0])
    return fallback if fallback else None


def _build_question_prompt(sentence: str, answer: str, kind: str, clue: str = ""):
    if kind == "definition" and clue:
        return f"Which term is described by this statement? {clue}"
    if kind == "definition":
        return f"Which term is described by this statement? {sentence}"
    if kind == "topic":
        return f"What is the main concept discussed here? {sentence}"
    word_count = len(answer.split())
    if word_count <= 4 and len(answer) <= 28:
        return f"Fill in the blank: {_mask_phrase(sentence, answer)}"
    return f"Which option best matches this idea? {sentence}"


def _mask_phrase(sentence: str, phrase: str) -> str:
    if not phrase:
        return sentence
    masked = re.sub(
        rf"\b{re.escape(phrase)}\b",
        "_____",
        sentence,
        count=1,
        flags=re.IGNORECASE,
    )
    return masked if masked != sentence else sentence.replace(phrase, "_____", 1)


def _is_good_distractor(candidate: str, answer: str) -> bool:
    candidate_norm = candidate.lower()
    answer_norm = answer.lower()
    if candidate_norm == answer_norm:
        return False
    if len(candidate_norm) < 3 or len(answer_norm) < 3:
        return False
    candidate_words = set(candidate_norm.split())
    answer_words = set(answer_norm.split())
    if candidate_words & answer_words:
        return False
    return True


def _quiz_prompt_for(sentence: str, answer: str) -> str:
    word_count = len(answer.split())
    if word_count <= 3 and len(answer) <= 24:
        return f"Fill the blank: {_mask_phrase(sentence, answer)}"
    return f"Best answer: {sentence}"


def _build_distractors(answer: str, answer_pool, term_frequency: Counter):
    answer_words = answer.lower().split()
    answer_size = len(answer_words)
    candidates = []

    for candidate in answer_pool:
        if not _is_good_distractor(candidate, answer):
            continue
        candidate_size = len(candidate.split())
        size_penalty = abs(candidate_size - answer_size)
        frequency_score = term_frequency.get(candidate.lower(), 0)
        candidates.append((size_penalty, -frequency_score, candidate))

    candidates.sort()
    distractors = []
    for _, __, candidate in candidates:
        if candidate not in distractors:
            distractors.append(candidate)
        if len(distractors) == 3:
            break

    if len(distractors) < 3:
        for fallback in QUIZ_GENERIC_CHOICES:
            if fallback not in distractors and _is_good_distractor(fallback, answer):
                distractors.append(fallback)
            if len(distractors) == 3:
                break

    return distractors


def _build_quiz_questions(text: str, limit: int = QUIZ_MAX_QUESTIONS):
    normalized = _normalize_quiz_text(_quiz_content_text(text))
    if not normalized:
        return []

    sentences = _split_quiz_sentences(normalized)
    tokens = _quiz_words(normalized)
    if not sentences or not tokens:
        return []

    frequency = Counter(tokens)
    phrase_frequency = Counter()
    for sentence in sentences:
        phrase_frequency.update(_phrase_candidates_for_sentence(sentence))

    candidate_rows = []
    for sentence in sentences:
        if _is_meta_quiz_sentence(sentence):
            continue

        subject_text, predicate_text = _extract_definition_pair(sentence)
        if subject_text and predicate_text:
            subject_bonus = 8 if any(part[:1].isupper() or part.isupper() for part in subject_text.split()) else 0
            candidate_rows.append({
                "sentence": sentence,
                "answer": subject_text,
                "question": _build_question_prompt(sentence, subject_text, "definition", clue=predicate_text),
                "kind": "definition",
                "score": _sentence_score(sentence) + (len(subject_text.split()) * 5) + min(len(predicate_text.split()), 6) + subject_bonus,
            })
            continue

        answer_text = _extract_salient_phrase(sentence, phrase_frequency, frequency)
        if not answer_text:
            continue

        answer_bonus = 8 if any(part[:1].isupper() or part.isupper() for part in answer_text.split()) else 0
        if len(answer_text.split()) == 1 and answer_text.lower() == answer_text:
            answer_bonus -= 3

        candidate_rows.append({
            "sentence": sentence,
            "answer": answer_text,
            "question": _build_question_prompt(sentence, answer_text, "topic"),
            "kind": "topic",
            "score": _sentence_score(sentence) + (len(answer_text.split()) * 5) + answer_bonus,
        })

    candidate_rows.sort(key=lambda row: row["score"], reverse=True)

    questions = []
    used_answers = set()
    answer_pool = [row["answer"] for row in candidate_rows]

    for row in candidate_rows:
        answer_text = row["answer"]
        answer_key = answer_text.lower()
        if answer_key in used_answers:
            continue

        distractors = _build_distractors(answer_text, answer_pool, frequency)
        options = [answer_text] + distractors
        options = list(dict.fromkeys(options))
        if len(options) < 4:
            continue

        random.shuffle(options)
        questions.append({
            "question": row["question"],
            "options": options,
            "answer": answer_text,
        })
        used_answers.add(answer_key)

        if len(questions) >= limit:
            break

    if questions:
        return questions

    # Fallback: if no pattern-based questions were found, use the highest-value terms.
    unique_terms = []
    for term, _ in frequency.most_common():
        if term not in unique_terms:
            unique_terms.append(term)

    for term in unique_terms:
        sentence = next((s for s in sentences if re.search(rf"\b{re.escape(term)}\b", s, re.IGNORECASE)), None)
        if not sentence:
            continue
        masked_sentence = _mask_phrase(sentence, term)
        distractors = _build_distractors(term, unique_terms, frequency)
        options = [term] + distractors
        options = list(dict.fromkeys(options))
        if len(options) < 4:
            continue
        random.shuffle(options)
        questions.append({
            "question": _quiz_prompt_for(sentence, term),
            "options": options,
            "answer": term,
        })
        if len(questions) >= limit:
            break

    return questions


def _fetch_quiz_attempts(user_id: int, limit: int = 10):
    conn = get_db()
    attempts = conn.execute(
        """
        SELECT id, user_id, source_name, total_questions, correct_answers, score,
               quiz_data, quiz_results, created_at
        FROM quiz_attempts
        WHERE user_id = ?
        ORDER BY datetime(created_at) DESC, id DESC
        LIMIT ?
        """,
        (user_id, limit),
    ).fetchall()
    conn.close()
    return attempts


def _build_quiz_pdf_bytes(title: str, quiz_questions, source_name: str = "", attempt=None, quiz_results=None):
    from reportlab.lib import colors
    from reportlab.lib.enums import TA_CENTER
    from reportlab.lib.pagesizes import A4
    from reportlab.lib.styles import ParagraphStyle, getSampleStyleSheet
    from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle

    buffer = io.BytesIO()
    document = SimpleDocTemplate(
        buffer,
        pagesize=A4,
        leftMargin=36,
        rightMargin=36,
        topMargin=42,
        bottomMargin=42,
        title=title,
    )

    styles = getSampleStyleSheet()
    styles.add(ParagraphStyle(
        name="QuizTitle",
        parent=styles["Title"],
        fontName="Helvetica-Bold",
        fontSize=20,
        leading=24,
        alignment=TA_CENTER,
        spaceAfter=8,
    ))
    styles.add(ParagraphStyle(
        name="QuizMeta",
        parent=styles["BodyText"],
        fontName="Helvetica",
        fontSize=9,
        leading=12,
        textColor=colors.HexColor("#4b5563"),
    ))
    styles.add(ParagraphStyle(
        name="QuizQuestion",
        parent=styles["BodyText"],
        fontName="Helvetica-Bold",
        fontSize=11,
        leading=14,
        spaceAfter=6,
    ))
    styles.add(ParagraphStyle(
        name="QuizOption",
        parent=styles["BodyText"],
        fontName="Helvetica",
        fontSize=10,
        leading=13,
        leftIndent=10,
        spaceAfter=2,
    ))

    story = [
        Paragraph(title, styles["QuizTitle"]),
        Paragraph(f"Generated on {datetime.now().strftime('%Y-%m-%d %H:%M')}", styles["QuizMeta"]),
    ]
    if source_name:
        story.append(Paragraph(f"Source: {source_name}", styles["QuizMeta"]))
    if attempt:
        story.append(Paragraph(
            f"Score: {attempt['score']}% | Correct: {attempt['correct_answers']}/{attempt['total_questions']}",
            styles["QuizMeta"],
        ))
    story.append(Spacer(1, 14)) # type: ignore

    for index, question in enumerate(quiz_questions, start=1):
        story.append(Paragraph(f"Question {index}", styles["QuizQuestion"]))
        story.append(Paragraph(question.get("question", ""), styles["BodyText"]))
        story.append(Spacer(1, 6)) # type: ignore

        options = question.get("options", [])
        option_rows = [[Paragraph(f"• {option}", styles["QuizOption"])] for option in options]
        if option_rows:
            table = Table(option_rows, colWidths=[460])
            table.setStyle(TableStyle([
                ("BACKGROUND", (0, 0), (-1, -1), colors.whitesmoke),
                ("BOX", (0, 0), (-1, -1), 0.4, colors.HexColor("#cbd5e1")),
                ("INNERGRID", (0, 0), (-1, -1), 0.25, colors.HexColor("#e2e8f0")),
                ("LEFTPADDING", (0, 0), (-1, -1), 8),
                ("RIGHTPADDING", (0, 0), (-1, -1), 8),
                ("TOPPADDING", (0, 0), (-1, -1), 6),
                ("BOTTOMPADDING", (0, 0), (-1, -1), 6),
            ]))
            story.append(table) # type: ignore

        if quiz_results:
            result = quiz_results[index - 1] if index - 1 < len(quiz_results) else {}
            selected = result.get("selected", "")
            correct = result.get("correct", question.get("answer", ""))
            status = "Correct" if result.get("is_correct") else "Incorrect"
            story.append(Spacer(1, 6)) # type: ignore
            story.append(Paragraph(f"Answer: {selected or 'No answer selected'}", styles["QuizMeta"]))
            story.append(Paragraph(f"Correct: {correct}", styles["QuizMeta"]))
            story.append(Paragraph(f"Status: {status}", styles["QuizMeta"]))

        story.append(Spacer(1, 14)) # type: ignore

    document.build(story) # type: ignore
    buffer.seek(0)
    return buffer.getvalue()


def _quiz_pdf_response(filename: str, pdf_bytes: bytes):
    response = make_response(pdf_bytes)
    response.headers["Content-Type"] = "application/pdf"
    response.headers["Content-Disposition"] = f'attachment; filename="{filename}"'
    return response


def init_db():
    """Create all tables if they do not yet exist."""
    conn = get_db()
    conn.executescript("""
        CREATE TABLE IF NOT EXISTS users (
            id         INTEGER PRIMARY KEY AUTOINCREMENT,
            name       TEXT    NOT NULL,
            email      TEXT    UNIQUE NOT NULL,
            password   TEXT    NOT NULL,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        );

        CREATE TABLE IF NOT EXISTS subjects (
            id             INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id        INTEGER NOT NULL,
            subject_name   TEXT    NOT NULL,
            difficulty     TEXT    NOT NULL,
            exam_date      DATE    NOT NULL,
            required_hours REAL    NOT NULL,
            daily_hours    REAL    NOT NULL,
            FOREIGN KEY (user_id) REFERENCES users(id)
        );

        CREATE TABLE IF NOT EXISTS tasks (
            id         INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id    INTEGER NOT NULL,
            task_name  TEXT    NOT NULL,
            subject    TEXT    NOT NULL,
            deadline   DATE    NOT NULL,
            status     TEXT    DEFAULT 'Pending',
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES users(id)
        );

        CREATE TABLE IF NOT EXISTS study_sessions (
            id      INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            subject TEXT    NOT NULL,
            hours   REAL    NOT NULL,
            date    DATE    NOT NULL,
            FOREIGN KEY (user_id) REFERENCES users(id)
        );

        CREATE TABLE IF NOT EXISTS schedules (
            id          INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id     INTEGER NOT NULL,
            date        DATE    NOT NULL,
            subject     TEXT    NOT NULL,
            study_hours REAL    NOT NULL,
            scheduled_time TEXT,
            completed   INTEGER DEFAULT 0,
            FOREIGN KEY (user_id) REFERENCES users(id)
        );

        CREATE TABLE IF NOT EXISTS quiz_attempts (
            id              INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id         INTEGER NOT NULL,
            source_name     TEXT    DEFAULT '',
            total_questions INTEGER NOT NULL,
            correct_answers INTEGER NOT NULL,
            score           INTEGER NOT NULL,
            quiz_data       TEXT    NOT NULL,
            quiz_results    TEXT    NOT NULL,
            created_at      TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES users(id)
        );
    """)
    conn.commit()
    conn.close()
    # Ensure users table has daily_hours_allowed column for per-user daily limit
    conn = sqlite3.connect(DATABASE)
    conn.row_factory = sqlite3.Row
    cols = [r[1] for r in conn.execute("PRAGMA table_info(users)").fetchall()]
    if 'daily_hours_allowed' not in cols:
        conn.execute("ALTER TABLE users ADD COLUMN daily_hours_allowed REAL DEFAULT 6.0")
        conn.commit()
    # Add timer-related columns if missing
    cols = [r[1] for r in conn.execute("PRAGMA table_info(users)").fetchall()]
    if 'timer_focus' not in cols:
        conn.execute("ALTER TABLE users ADD COLUMN timer_focus INTEGER DEFAULT 25")
    if 'timer_short' not in cols:
        conn.execute("ALTER TABLE users ADD COLUMN timer_short INTEGER DEFAULT 5")
    if 'timer_long' not in cols:
        conn.execute("ALTER TABLE users ADD COLUMN timer_long INTEGER DEFAULT 15")
    if 'timer_sessions_before_long' not in cols:
        conn.execute("ALTER TABLE users ADD COLUMN timer_sessions_before_long INTEGER DEFAULT 4")
    if 'timer_expanded' not in cols:
        conn.execute("ALTER TABLE users ADD COLUMN timer_expanded INTEGER DEFAULT 0")
    conn.commit()
    conn.close()
    # Add profile fields if missing
    conn = sqlite3.connect(DATABASE)
    conn.row_factory = sqlite3.Row
    cols = [r[1] for r in conn.execute("PRAGMA table_info(users)").fetchall()]
    if 'class_name' not in cols:
        conn.execute("ALTER TABLE users ADD COLUMN class_name TEXT DEFAULT ''")
    if 'age' not in cols:
        conn.execute("ALTER TABLE users ADD COLUMN age INTEGER DEFAULT NULL")
    if 'avatar' not in cols:
        conn.execute("ALTER TABLE users ADD COLUMN avatar TEXT DEFAULT ''")
    if 'receive_emails' not in cols:
        conn.execute("ALTER TABLE users ADD COLUMN receive_emails INTEGER DEFAULT 1")
    conn.commit()
    conn.close()

    conn = sqlite3.connect(DATABASE)
    conn.row_factory = sqlite3.Row
    cols = [r[1] for r in conn.execute("PRAGMA table_info(schedules)").fetchall()]
    if 'scheduled_time' not in cols:
        conn.execute("ALTER TABLE schedules ADD COLUMN scheduled_time TEXT")
        conn.commit()
    conn.close()


# Initialize database tables when the module is imported so serverless hosts
# have the schema available without relying on __main__ startup code.
init_db()


def auto_reschedule_missed_sessions(user_id: int, conn) -> int:
    """
    Auto-reschedule missed schedule entries (date < today and not completed).

    Rules:
    - Keep each session's original hours.
    - Move to earliest future day with remaining capacity (max 8h/day).
    - Never place on/after the subject's exam date when known.
    Returns number of sessions moved.
    """
    today = date.today()
    today_str = today.strftime("%Y-%m-%d")

    missed = conn.execute(
        """SELECT id, subject, study_hours, date
           FROM schedules
           WHERE user_id=? AND completed=0 AND date < ?
           ORDER BY date, id""",
        (user_id, today_str),
    ).fetchall()

    if not missed:
        return 0

    subject_exams = {
        row["subject_name"]: datetime.strptime(row["exam_date"], "%Y-%m-%d").date()
        for row in conn.execute(
            "SELECT subject_name, exam_date FROM subjects WHERE user_id= ?", (user_id,)
        ).fetchall()
    }

    moved = 0
    for row in missed:
        session_hours = float(row["study_hours"])
        subject_name = row["subject"]
        exam_date = subject_exams.get(subject_name, today + timedelta(days=60))

        # Search upcoming days; avoid scheduling on/after exam date.
        for offset in range(0, 60):
            candidate = today + timedelta(days=offset)
            if candidate >= exam_date:
                break

            cstr = candidate.strftime("%Y-%m-%d")
            planned = conn.execute(
                """SELECT COALESCE(SUM(study_hours),0) AS t
                   FROM schedules
                   WHERE user_id=? AND date=? AND id != ?""",
                (user_id, cstr, row["id"]),
            ).fetchone()["t"]

            if float(planned) + session_hours <= 8.0:
                conn.execute(
                    "UPDATE schedules SET date=? WHERE id=? AND user_id=?",
                    (cstr, row["id"], user_id),
                )
                moved += 1
                break

    return moved


def regenerate_user_schedule(user_id: int, conn) -> int:
    """Rebuild schedules for a user from current subjects and return row count."""
    subs = conn.execute(
        "SELECT * FROM subjects WHERE user_id=? ORDER BY exam_date", (user_id,)
    ).fetchall()
    subjects_data = [dict(s) for s in subs]

    conn.execute("DELETE FROM schedules WHERE user_id=?", (user_id,))
    if not subjects_data:
        return 0

    schedule = generate_schedule(subjects_data)
    for entry in schedule:
        conn.execute(
            "INSERT INTO schedules (user_id, date, subject, study_hours) VALUES (?,?,?,?)",
            (user_id, entry["date"], entry["subject"], entry["hours"]),
        )
    return len(schedule)


# ── Auth decorator ────────────────────────────────────────────────────────────
def login_required(f):
    """Redirect unauthenticated requests to the login page."""
    @wraps(f)
    def decorated(*args, **kwargs):
        if "user_id" not in session:
            flash("Please login to continue.", "warning")
            return redirect(url_for("login"))
        return f(*args, **kwargs)
    return decorated


# ── Jinja2 helper filter ─────────────────────────────────────────────────────
@app.template_filter("days_until")
def days_until_filter(date_str):
    """Return # of days from today until given date string (YYYY-MM-DD)."""
    try:
        target = datetime.strptime(date_str, "%Y-%m-%d").date()
        return (target - date.today()).days
    except Exception:
        return 0


@app.context_processor
def inject_user_timer_settings():
    """Provide per-user timer and daily-limit settings to all templates."""
    if 'user_id' not in session:
        return {}
    try:
        conn = get_db()
        row = conn.execute(
            """
            SELECT COALESCE(daily_hours_allowed,6.0) AS daily,
                   COALESCE(timer_focus,25) AS timer_focus,
                   COALESCE(timer_short,5) AS timer_short,
                   COALESCE(timer_long,15) AS timer_long,
                   COALESCE(timer_sessions_before_long,4) AS timer_sessions_before_long
            FROM users WHERE id=?
            """,
            (session['user_id'],),
        ).fetchone()
        conn.close()
        if not row:
            return {}
        return {
            'daily_limit': round(float(row['daily']), 1),
            'timer_focus': int(row['timer_focus']),
            'timer_short': int(row['timer_short']),
            'timer_long': int(row['timer_long']),
            'timer_sessions_before_long': int(row['timer_sessions_before_long']),
            'timer_expanded': int(row['timer_expanded']) if row['timer_expanded'] is not None else 0,
        }
    except Exception:
        return {}


@app.route('/api/timer-layout', methods=['POST'])
@login_required
def save_timer_layout():
    """Persist timer widget layout state for the current user."""
    data = request.get_json(silent=True) or {}
    expanded = 1 if data.get('expanded') else 0
    conn = get_db()
    try:
        conn.execute('UPDATE users SET timer_expanded=? WHERE id=?', (expanded, session['user_id']))
        conn.commit()
        return jsonify({'status': 'ok', 'expanded': bool(expanded)})
    except sqlite3.Error as e:
        conn.rollback()
        return jsonify({'status': 'error', 'message': str(e)}), 500
    finally:
        conn.close()


# ── Authentication routes ─────────────────────────────────────────────────────
@app.route("/login", methods=["GET", "POST"])
def login():
    if "user_id" in session:
        return redirect(url_for("dashboard"))

    if request.method == "POST":
        email    = request.form.get("email", "").strip()
        password = request.form.get("password", "")

        conn = get_db()
        user = conn.execute(
            "SELECT * FROM users WHERE email = ?", (email,)
        ).fetchone()
        conn.close()

        if user and check_password_hash(user["password"], password):
            session["user_id"]   = user["id"]
            session["user_name"] = user["name"]
            session["user_avatar"] = (user["avatar"] if "avatar" in user.keys() else '') or ''
            flash(f"Welcome back, {user['name']}! 🎉", "success")
            return redirect(url_for("dashboard"))

        flash("Invalid email or password.", "danger")

    return render_template("login.html")


@app.route("/signup", methods=["GET", "POST"])
def signup():
    if "user_id" in session:
        return redirect(url_for("dashboard"))

    if request.method == "POST":
        name     = request.form.get("name", "").strip()
        email    = request.form.get("email", "").strip()
        password = request.form.get("password", "")

        if len(password) < 6:
            flash("Password must be at least 6 characters.", "danger")
            return render_template("signup.html")

        hashed = generate_password_hash(password)
        try:
            conn = get_db()
            conn.execute(
                "INSERT INTO users (name, email, password) VALUES (?, ?, ?)",
                (name, email, hashed),
            )
            # Ensure daily_hours_allowed is set to default if column exists
            try:
                conn.execute(
                    "UPDATE users SET daily_hours_allowed = COALESCE(daily_hours_allowed, ?) WHERE email=?",
                    (6.0, email),
                )
            except Exception:
                pass
            conn.commit()
            conn.close()
            flash("Account created! Please log in.", "success")
            return redirect(url_for("login"))
        except sqlite3.IntegrityError:
            flash("Email already registered.", "danger")

    return render_template("signup.html")


@app.route("/logout")
def logout():
    session.clear()
    flash("You have been logged out.", "info")
    return redirect(url_for("login"))


# ── Public landing page ───────────────────────────────────────────────────────
@app.route("/")
def index():
    if "user_id" in session:
        return redirect(url_for("dashboard"))
    return render_template("index.html")


# ── Dashboard ─────────────────────────────────────────────────────────────────
@app.route("/dashboard")
@login_required
def dashboard():
    uid   = session["user_id"]
    today = date.today().strftime("%Y-%m-%d")
    conn  = get_db()

    # Feature: auto-reschedule missed study sessions
    rescheduled_count = auto_reschedule_missed_sessions(uid, conn)
    if rescheduled_count > 0:
        conn.commit()

    today_schedule = conn.execute(
        "SELECT * FROM schedules WHERE user_id=? AND date=? ORDER BY subject",
        (uid, today),
    ).fetchall()

    pending_tasks = conn.execute(
        "SELECT * FROM tasks WHERE user_id=? AND status='Pending' ORDER BY deadline LIMIT 5",
        (uid,),
    ).fetchall()

    total_tasks = conn.execute(
        "SELECT COUNT(*) AS c FROM tasks WHERE user_id=?", (uid,)
    ).fetchone()["c"]

    completed_count = conn.execute(
        "SELECT COUNT(*) AS c FROM tasks WHERE user_id=? AND status='Completed'", (uid,)
    ).fetchone()["c"]

    today_hours = conn.execute(
        "SELECT COALESCE(SUM(hours),0) AS t FROM study_sessions WHERE user_id=? AND date=?",
        (uid, today),
    ).fetchone()["t"]

    completed_schedule_hours_today = conn.execute(
        "SELECT COALESCE(SUM(study_hours),0) AS t FROM schedules WHERE user_id=? AND date=? AND completed=1",
        (uid, today),
    ).fetchone()["t"]

    today_hours = max(float(today_hours), float(completed_schedule_hours_today))

    # User's daily available hours (fallback to 6.0)
    try:
        row = conn.execute("SELECT daily_hours_allowed FROM users WHERE id=?", (uid,)).fetchone()
        daily_limit = float(row["daily_hours_allowed"]) if row and row["daily_hours_allowed"] is not None else 6.0
    except Exception:
        daily_limit = 6.0

    # Planned schedule hours for today
    planned_today = conn.execute(
        "SELECT COALESCE(SUM(study_hours),0) AS t FROM schedules WHERE user_id=? AND date=?",
        (uid, today),
    ).fetchone()["t"]

    productivity = calculate_productivity_score(uid, conn)
    weekly_data  = get_weekly_stats(uid, conn)
    streak       = get_study_streak(uid, conn)
    motivation   = get_motivational_message(productivity)

    upcoming = conn.execute(
        """SELECT task_name, subject, deadline FROM tasks
           WHERE user_id=? AND status='Pending'
           AND deadline >= ? AND deadline <= date(?, '+3 days')
           ORDER BY deadline""",
        (uid, today, today),
    ).fetchall()

    conn.close()

    return render_template(
        "dashboard.html",
        today_schedule=today_schedule,
        pending_tasks=pending_tasks,
        completed_count=completed_count,
        total_tasks=total_tasks,
        productivity=productivity,
        today_hours=round(today_hours, 1),
        weekly_data=weekly_data,
        streak=streak,
        motivation=motivation,
        upcoming=upcoming,
        rescheduled_count=rescheduled_count,
        daily_limit=round(daily_limit,1),
        planned_today=round(planned_today,1),
    )


# ── Subjects ──────────────────────────────────────────────────────────────────
@app.route("/subjects", methods=["GET", "POST"])
@login_required
def subjects():
    uid = session["user_id"]

    if request.method == "POST":
        sname    = request.form.get("subject_name", "").strip()
        diff     = request.form.get("difficulty", "").strip()
        edate    = request.form.get("exam_date", "").strip()
        req_raw  = request.form.get("required_hours", "").strip()
        day_raw  = request.form.get("daily_hours", "").strip()

        if not all([sname, diff, edate, req_raw, day_raw]):
            flash("Please fill all required subject fields.", "warning")
            return redirect(url_for("subjects"))

        if diff not in {"Easy", "Medium", "Hard"}:
            flash("Invalid difficulty selected.", "danger")
            return redirect(url_for("subjects"))

        try:
            req_hrs = float(req_raw)
            day_hrs = float(day_raw)
        except ValueError:
            flash("Please enter valid numeric hours.", "danger")
            return redirect(url_for("subjects"))

        if req_hrs <= 0 or day_hrs <= 0:
            flash("Study hours must be greater than 0.", "warning")
            return redirect(url_for("subjects"))

        try:
            exam_dt = datetime.strptime(edate, "%Y-%m-%d").date()
        except ValueError:
            flash("Please choose a valid exam date.", "danger")
            return redirect(url_for("subjects"))

        if exam_dt < date.today():
            flash("Exam date cannot be in the past.", "warning")
            return redirect(url_for("subjects"))

        # Minimum daily hours needed to finish before exam date.
        days_left = max((exam_dt - date.today()).days, 1)
        min_daily_needed = req_hrs / days_left
        if day_hrs < min_daily_needed:
            day_hrs = round(min_daily_needed, 1)
            flash(
                f"Daily hours auto-adjusted to minimum {day_hrs}h/day based on total hours and exam date.",
                "info",
            )

        conn = get_db()
        conn.execute(
            """INSERT INTO subjects
               (user_id, subject_name, difficulty, exam_date, required_hours, daily_hours)
               VALUES (?, ?, ?, ?, ?, ?)""",
            (uid, sname, diff, edate, req_hrs, day_hrs),
        )

        # Auto-regenerate schedule so new subjects appear immediately in planner graph.
        scheduled_sessions = regenerate_user_schedule(uid, conn)

        conn.commit()
        conn.close()
        flash(f'Subject "{sname}" added!', "success")
        flash(f"Schedule auto-updated with {scheduled_sessions} planned session(s).", "info")
        return redirect(url_for("subjects"))

    conn  = get_db()
    subs  = conn.execute(
        "SELECT * FROM subjects WHERE user_id=? ORDER BY exam_date", (uid,)
    ).fetchall()
    conn.close()

    return render_template(
        "subjects.html",
        subjects=subs,
        today=date.today().strftime("%Y-%m-%d"),
    )


@app.route("/subjects/delete/<int:sid>")
@login_required
def delete_subject(sid):
    conn = get_db()
    conn.execute(
        "DELETE FROM subjects WHERE id=? AND user_id=?", (sid, session["user_id"])
    )

    # Keep schedule synced after subject removal.
    scheduled_sessions = regenerate_user_schedule(session["user_id"], conn)

    conn.commit()
    conn.close()
    flash("Subject removed.", "info")
    flash(f"Schedule re-generated with {scheduled_sessions} session(s).", "info")
    return redirect(url_for("subjects"))


# ── Planner (AI schedule generator) ──────────────────────────────────────────
@app.route("/planner")
@login_required
def planner():
    uid  = session["user_id"]
    conn = get_db()

    subs = conn.execute(
        "SELECT * FROM subjects WHERE user_id=? ORDER BY exam_date", (uid,)
    ).fetchall()

    schedules = conn.execute(
        "SELECT * FROM schedules WHERE user_id=? ORDER BY date", (uid,)
    ).fetchall()

    conn.close()

    subjects_data = [dict(s) for s in subs]
    schedule_rows = [dict(s) for s in schedules]

    # Table rows: include placeholders for subjects that got no schedule slot.
    scheduled_subjects = {row["subject"] for row in schedule_rows}
    schedule_table_rows = []

    for row in schedule_rows:
        row_copy = dict(row)
        row_copy["is_placeholder"] = False
        schedule_table_rows.append(row_copy)

    for sub in subjects_data:
        if sub["subject_name"] not in scheduled_subjects:
            schedule_table_rows.append({
                "id": None,
                "date": "",
                "subject": sub["subject_name"],
                "study_hours": 0,
                "completed": 0,
                "is_placeholder": True,
            })

    # Keep scheduled rows first, then placeholders sorted by subject name.
    scheduled_part = [r for r in schedule_table_rows if not r["is_placeholder"]]
    placeholder_part = sorted(
        [r for r in schedule_table_rows if r["is_placeholder"]],
        key=lambda x: x["subject"].lower(),
    )
    schedule_table_rows = scheduled_part + placeholder_part
    schedule_unallocated_count = len(placeholder_part)

    # Build live priority breakdown for the UI
    priority_breakdown = get_priority_breakdown(subjects_data)

    # Build per-subject schedule breakdown (required hours, deadline, allocated, gap)
    allocated_by_subject = defaultdict(float)
    for row in schedule_rows:
        allocated_by_subject[row["subject"]] += float(row["study_hours"])

    subject_summary = []
    total_required = 0.0
    total_allocated = 0.0

    for sub in subjects_data:
        required_hours = round(float(sub["required_hours"]), 1)
        allocated_hours = round(float(allocated_by_subject.get(sub["subject_name"], 0.0)), 1)
        remaining_hours = round(max(required_hours - allocated_hours, 0.0), 1)

        try:
            days_left = (datetime.strptime(sub["exam_date"], "%Y-%m-%d").date() - date.today()).days
        except Exception:
            days_left = 0

        coverage_pct = round((allocated_hours / required_hours) * 100, 1) if required_hours > 0 else 0

        subject_summary.append({
            "subject": sub["subject_name"],
            "deadline": sub["exam_date"],
            "required_hours": required_hours,
            "allocated_hours": allocated_hours,
            "remaining_hours": remaining_hours,
            "daily_hours": round(float(sub["daily_hours"]), 1),
            "days_left": days_left,
            "coverage_pct": min(coverage_pct, 100.0),
        })

        total_required += required_hours
        total_allocated += allocated_hours

    subject_summary.sort(key=lambda x: x["deadline"])

    # Planner productivity graph: planned vs completed schedule hours (last 7 days)
    planner_productivity = {
        "dates": [],
        "planned": [],
        "completed": [],
        "completion_pct": [],
    }

    for i in range(6, -1, -1):
        d = (date.today() - timedelta(days=i)).strftime("%Y-%m-%d")
        day_rows = [r for r in schedule_rows if r["date"] == d]

        planned_hours = round(sum(float(r["study_hours"]) for r in day_rows), 2)
        completed_hours = round(
            sum(float(r["study_hours"]) for r in day_rows if int(r["completed"]) == 1),
            2,
        )
        completion_pct = round((completed_hours / planned_hours) * 100, 1) if planned_hours > 0 else 0

        planner_productivity["dates"].append(d)
        planner_productivity["planned"].append(planned_hours)
        planner_productivity["completed"].append(completed_hours)
        planner_productivity["completion_pct"].append(completion_pct)

    planner_metrics = {
        "total_required": round(total_required, 1),
        "total_allocated": round(total_allocated, 1),
        "coverage_pct": round((total_allocated / total_required) * 100, 1) if total_required > 0 else 0,
    }

    # Subject-wise generated schedule graph data
    planner_subject_graph = {
        "labels": [row["subject"] for row in subject_summary],
        "required": [row["required_hours"] for row in subject_summary],
        "allocated": [row["allocated_hours"] for row in subject_summary],
    }

    return render_template(
        "planner.html",
        subjects=subs,
        schedules=schedules,
        schedule_table_rows=schedule_table_rows,
        schedule_table_rows_today=[r for r in schedule_table_rows if (safe_get(r, 'date') == date.today().strftime('%Y-%m-%d'))],
        schedule_table_rows_remaining=[r for r in schedule_table_rows if (safe_get(r, 'date') != date.today().strftime('%Y-%m-%d'))],
        schedule_unallocated_count=schedule_unallocated_count,
        priority_breakdown=priority_breakdown,
        subject_summary=subject_summary,
        planner_productivity=planner_productivity,
        planner_metrics=planner_metrics,
        planner_subject_graph=planner_subject_graph,
        today_str=date.today().strftime("%Y-%m-%d"),
        now_time=datetime.now().strftime("%H:%M"),
    )


@app.route("/planner/remaining")
@login_required
def planner_remaining():
    uid = session["user_id"]
    conn = get_db()

    subs = conn.execute(
        "SELECT * FROM subjects WHERE user_id=? ORDER BY exam_date", (uid,)
    ).fetchall()

    schedules = conn.execute(
        "SELECT * FROM schedules WHERE user_id=? ORDER BY date", (uid,)
    ).fetchall()

    conn.close()

    subjects_data = [dict(s) for s in subs]
    schedule_rows = [dict(s) for s in schedules]

    # Build schedule table rows (including placeholders)
    scheduled_subjects = {row["subject"] for row in schedule_rows}
    schedule_table_rows = []
    for row in schedule_rows:
        row_copy = dict(row)
        row_copy["is_placeholder"] = False
        schedule_table_rows.append(row_copy)
    for sub in subjects_data:
        if sub["subject_name"] not in scheduled_subjects:
            schedule_table_rows.append({
                "id": None,
                "date": "",
                "subject": sub["subject_name"],
                "study_hours": 0,
                "completed": 0,
                "is_placeholder": True,
            })

    # Remaining rows = those not for today
    today_str = date.today().strftime("%Y-%m-%d")
    remaining_rows = [r for r in schedule_table_rows if safe_get(r, 'date') != today_str]

    return render_template(
        "remaining_schedule.html",
        subjects=subs,
        schedules=schedules,
        remaining_rows=remaining_rows,
        today_str=today_str,
        now_time=datetime.now().strftime("%H:%M"),
    )


@app.route("/planner/reschedule-missed", methods=["POST"])
@login_required
def planner_reschedule_missed():
    """Manual trigger for missed-session auto-rescheduling."""
    conn = get_db()
    moved = auto_reschedule_missed_sessions(session["user_id"], conn)
    conn.commit()
    conn.close()

    if moved > 0:
        flash(f"📅 Rescheduled {moved} missed study session(s).", "success")
    else:
        flash("No missed sessions to reschedule.", "info")
    return redirect(url_for("planner"))


@app.route("/generate-schedule", methods=["POST"])
@login_required
def generate_schedule_route():
    uid  = session["user_id"]
    conn = get_db()

    subs = conn.execute(
        "SELECT * FROM subjects WHERE user_id=?", (uid,)
    ).fetchall()

    if not subs:
        flash("Add at least one subject before generating a schedule.", "warning")
        conn.close()
        return redirect(url_for("subjects"))

    schedule_count = regenerate_user_schedule(uid, conn)

    conn.commit()
    conn.close()
    flash(f"✅ Schedule generated — {schedule_count} study sessions planned!", "success")
    return redirect(url_for("planner"))


@app.route("/schedule/toggle/<int:sid>", methods=["POST"])
@login_required
def toggle_schedule_status(sid):
    """Toggle a schedule session between Pending and Done."""
    uid = session["user_id"]
    conn = get_db()

    row = conn.execute(
        "SELECT completed, date FROM schedules WHERE id=? AND user_id=?", (sid, uid)
    ).fetchone()

    if row:
        new_state = 0 if int(row["completed"]) == 1 else 1

        # Do not allow marking future sessions as done.
        if new_state == 1:
            try:
                session_date = datetime.strptime(row["date"], "%Y-%m-%d").date()
            except ValueError:
                session_date = date.today()

            if session_date > date.today():
                conn.close()
                flash("You can mark a session as done only on or after its scheduled date.", "warning")
                return redirect(request.referrer or url_for("planner"))

        conn.execute(
            "UPDATE schedules SET completed=? WHERE id=? AND user_id=?",
            (new_state, sid, uid),
        )
        conn.commit()
        flash("Schedule session updated.", "success")

    conn.close()
    return redirect(request.referrer or url_for("planner"))


@app.route("/schedule/time/<int:sid>", methods=["POST"])
@login_required
def update_schedule_time(sid):
    """Save a study time for one schedule row."""
    time_value = request.form.get("scheduled_time", "").strip()

    if time_value:
        try:
            datetime.strptime(time_value, "%H:%M")
        except ValueError:
            flash("Please enter a valid time in HH:MM format.", "warning")
            return redirect(request.referrer or url_for("planner"))

    conn = get_db()
    try:
        conn.execute(
            "UPDATE schedules SET scheduled_time=? WHERE id=? AND user_id=?",
            (time_value or None, sid, session["user_id"]),
        )
        conn.commit()
        flash("Schedule time saved.", "success")
    except sqlite3.Error as e:
        conn.rollback()
        flash(f"Failed to save schedule time: {e}", "danger")
    finally:
        conn.close()

    return redirect(request.referrer or url_for("planner"))


# ── Tasks ─────────────────────────────────────────────────────────────────────
@app.route("/tasks")
@login_required
def tasks():
    uid  = session["user_id"]
    conn = get_db()

    all_tasks = conn.execute(
        "SELECT * FROM tasks WHERE user_id=? ORDER BY deadline", (uid,)
    ).fetchall()

    subject_names = conn.execute(
        "SELECT DISTINCT subject_name FROM subjects WHERE user_id=?", (uid,)
    ).fetchall()

    conn.close()
    return render_template(
        "tasks.html",
        tasks=all_tasks,
        subject_names=subject_names,
        today=date.today().strftime("%Y-%m-%d"),
    )


@app.route("/tasks/add", methods=["POST"])
@login_required
def add_task():
    uid      = session["user_id"]
    tname    = request.form.get("task_name", "").strip()
    subject  = request.form.get("subject", "").strip()
    deadline = request.form.get("deadline", "").strip()

    if not all([tname, subject, deadline]):
        flash("Please fill all required task fields.", "warning")
        return redirect(url_for("tasks"))

    try:
        deadline_dt = datetime.strptime(deadline, "%Y-%m-%d").date()
    except ValueError:
        flash("Please choose a valid deadline date.", "danger")
        return redirect(url_for("tasks"))

    if deadline_dt < date.today():
        flash("Deadline cannot be in the past.", "warning")
        return redirect(url_for("tasks"))

    conn = get_db()
    try:
        conn.execute(
            "INSERT INTO tasks (user_id, task_name, subject, deadline, status) VALUES (?,?,?,?,'Pending')",
            (uid, tname, subject, deadline),
        )
        conn.commit()
        conn.close()
        flash("Task added!", "success")
        return redirect(url_for("tasks"))
    except sqlite3.Error as e:
        try:
            conn.rollback()
        except Exception:
            pass
        conn.close()
        flash(f"Failed to add task: {e}", "danger")
        return redirect(url_for("tasks"))


@app.route("/tasks/edit/<int:tid>", methods=["POST"])
@login_required
def edit_task(tid):
    tname    = request.form.get("task_name", "").strip()
    subject  = request.form.get("subject", "").strip()
    deadline = request.form.get("deadline", "").strip()

    if not all([tname, subject, deadline]):
        flash("Please fill all required task fields.", "warning")
        return redirect(url_for("tasks"))

    try:
        deadline_dt = datetime.strptime(deadline, "%Y-%m-%d").date()
    except ValueError:
        flash("Please choose a valid deadline date.", "danger")
        return redirect(url_for("tasks"))

    if deadline_dt < date.today():
        flash("Deadline cannot be in the past.", "warning")
        return redirect(url_for("tasks"))

    conn = get_db()
    try:
        conn.execute(
            "UPDATE tasks SET task_name=?, subject=?, deadline=? WHERE id=? AND user_id=?",
            (tname, subject, deadline, tid, session["user_id"]),
        )
        conn.commit()
        conn.close()
        flash("Task updated!", "success")
        return redirect(url_for("tasks"))
    except sqlite3.Error as e:
        try:
            conn.rollback()
        except Exception:
            pass
        conn.close()
        flash(f"Failed to update task: {e}", "danger")
        return redirect(url_for("tasks"))


@app.route("/tasks/delete/<int:tid>")
@login_required
def delete_task(tid):
    conn = get_db()
    try:
        conn.execute(
            "DELETE FROM tasks WHERE id=? AND user_id=?", (tid, session["user_id"])
        )
        conn.commit()
        conn.close()
        flash("Task deleted.", "info")
        return redirect(url_for("tasks"))
    except sqlite3.Error as e:
        try:
            conn.rollback()
        except Exception:
            pass
        conn.close()
        flash(f"Failed to delete task: {e}", "danger")
        return redirect(url_for("tasks"))


@app.route("/tasks/complete/<int:tid>")
@login_required
def complete_task(tid):
    conn = get_db()
    try:
        conn.execute(
            "UPDATE tasks SET status='Completed' WHERE id=? AND user_id=?",
            (tid, session["user_id"]),
        )
        conn.commit()
        # Compute updated completion rate for feedback
        try:
            completed = conn.execute(
                "SELECT COUNT(*) AS c FROM tasks WHERE user_id=? AND status='Completed'",
                (session["user_id"],),
            ).fetchone()["c"]
            total = conn.execute(
                "SELECT COUNT(*) AS c FROM tasks WHERE user_id=?",
                (session["user_id"],),
            ).fetchone()["c"]
            pct = round(completed / total * 100, 1) if total and total > 0 else 0
            flash(f"🎉 Task completed! Productivity: {pct}% ({completed}/{total} tasks completed)", "success")
        except Exception:
            flash("🎉 Task completed! Great work!", "success")
        finally:
            conn.close()
        return redirect(url_for("tasks"))
    except sqlite3.Error as e:
        try:
            conn.rollback()
        except Exception:
            pass
        conn.close()
        flash(f"Failed to complete task: {e}", "danger")
        return redirect(url_for("tasks"))


@app.route("/manage-data")
@login_required
def manage_data():
    uid = session["user_id"]
    conn = get_db()

    counts = {
        "subjects": conn.execute(
            "SELECT COUNT(*) AS c FROM subjects WHERE user_id=?", (uid,)
        ).fetchone()["c"],
        "tasks": conn.execute(
            "SELECT COUNT(*) AS c FROM tasks WHERE user_id=?", (uid,)
        ).fetchone()["c"],
        "completed_tasks": conn.execute(
            "SELECT COUNT(*) AS c FROM tasks WHERE user_id=? AND status='Completed'", (uid,)
        ).fetchone()["c"],
        "study_sessions": conn.execute(
            "SELECT COUNT(*) AS c FROM study_sessions WHERE user_id=?", (uid,)
        ).fetchone()["c"],
        "schedules": conn.execute(
            "SELECT COUNT(*) AS c FROM schedules WHERE user_id=?", (uid,)
        ).fetchone()["c"],
    }

    conn.close()
    return render_template("manage_data.html", counts=counts)


@app.route("/manage-data/action", methods=["POST"])
@login_required
def manage_data_action():
    uid = session["user_id"]
    action = request.form.get("action", "").strip()
    confirm = request.form.get("confirm", "").strip().upper()

    action_queries = {
        "clear_completed_tasks": [
            ("DELETE FROM tasks WHERE user_id=? AND status='Completed'", (uid,)),
        ],
        "clear_tasks": [
            ("DELETE FROM tasks WHERE user_id=?", (uid,)),
        ],
        "clear_sessions": [
            ("DELETE FROM study_sessions WHERE user_id=?", (uid,)),
        ],
        "clear_schedules": [
            ("DELETE FROM schedules WHERE user_id=?", (uid,)),
        ],
        "clear_subjects": [
            ("DELETE FROM schedules WHERE user_id=?", (uid,)),
            ("DELETE FROM subjects WHERE user_id=?", (uid,)),
        ],
        "reset_all": [
            ("DELETE FROM schedules WHERE user_id=?", (uid,)),
            ("DELETE FROM study_sessions WHERE user_id=?", (uid,)),
            ("DELETE FROM tasks WHERE user_id=?", (uid,)),
            ("DELETE FROM subjects WHERE user_id=?", (uid,)),
        ],
    }

    if action not in action_queries:
        flash("Invalid data action.", "danger")
        return redirect(url_for("manage_data"))

    if action == "reset_all" and confirm != "DELETE":
        flash("Type DELETE to confirm full reset.", "warning")
        return redirect(url_for("manage_data"))

    conn = get_db()
    before = conn.total_changes
    for sql, params in action_queries[action]:
        conn.execute(sql, params)
    conn.commit()
    affected = conn.total_changes - before
    conn.close()

    action_names = {
        "clear_completed_tasks": "completed tasks",
        "clear_tasks": "all tasks",
        "clear_sessions": "study sessions",
        "clear_schedules": "study schedules",
        "clear_subjects": "subjects and schedules",
        "reset_all": "all study data",
    }
    flash(f"Deleted {affected} record(s) from {action_names[action]}.", "success")
    return redirect(url_for("manage_data"))


# ── Study session logging (JSON API) ─────────────────────────────────────────
@app.route("/study-session/log", methods=["POST"])
@login_required
def log_study_session():
    data    = request.get_json(silent=True) or {}
    uid     = session["user_id"]
    subject = data.get("subject", "").strip()
    try:
        hours = float(data.get("hours", 0))
    except (TypeError, ValueError):
        return jsonify({"status": "error", "message": "Invalid hours value."}), 400
    today   = date.today().strftime("%Y-%m-%d")

    if hours > 0 and subject:
        conn = get_db()
        conn.execute(
            "INSERT INTO study_sessions (user_id, subject, hours, date) VALUES (?,?,?,?)",
            (uid, subject, round(hours, 2), today),
        )

        # Feature: auto-mark one matching planned session as completed.
        scheduled = conn.execute(
            """SELECT id FROM schedules
               WHERE user_id=? AND subject=? AND date=? AND completed=0
               ORDER BY id LIMIT 1""",
            (uid, subject, today),
        ).fetchone()

        linked = False
        if scheduled:
            conn.execute(
                "UPDATE schedules SET completed=1 WHERE id=? AND user_id=?",
                (scheduled["id"], uid),
            )
            linked = True

        conn.commit()
        conn.close()
        return jsonify({
            "status": "ok",
            "message": f"Logged {hours:.2f}h for {subject}!",
            "linked_schedule": linked,
        })

    return jsonify({"status": "error", "message": "Invalid data."}), 400


@app.route("/api/subjects-list")
@login_required
def subjects_list():
    """Return a JSON list of subject names for the AI Study Planner timer dropdown."""
    uid  = session["user_id"]
    conn = get_db()
    rows = conn.execute(
        "SELECT DISTINCT subject_name FROM subjects WHERE user_id=?", (uid,)
    ).fetchall()
    conn.close()
    return jsonify([r["subject_name"] for r in rows])


@app.route("/api/schedule-info")
@login_required
def schedule_info():
    """Return the next planned schedule row for a subject."""
    uid = session["user_id"]
    subject = request.args.get("subject", "").strip()

    if not subject:
        return jsonify({"status": "error", "message": "Missing subject."}), 400

    conn = get_db()
    row = conn.execute(
        """
        SELECT date, subject, study_hours, completed, scheduled_time
        FROM schedules
        WHERE user_id=? AND subject=?
        ORDER BY date ASC, CASE WHEN scheduled_time IS NULL OR scheduled_time='' THEN 1 ELSE 0 END, scheduled_time ASC, id ASC
        LIMIT 1
        """,
        (uid, subject),
    ).fetchone()
    conn.close()

    if not row:
        return jsonify({"status": "ok", "found": False})

    return jsonify({
        "status": "ok",
        "found": True,
        "date": row["date"],
        "subject": row["subject"],
        "study_hours": row["study_hours"],
        "completed": int(row["completed"] or 0),
        "scheduled_time": row["scheduled_time"] or "",
    })
def _build_export_dataframe(uid: int, dataset: str, conn):
    """Return a pandas DataFrame for a supported export dataset."""
    if dataset == "sessions":
        return pd.read_sql_query(
            "SELECT date, subject, hours FROM study_sessions WHERE user_id=? ORDER BY date",
            conn,
            params=(uid,),
        )
    if dataset == "tasks":
        return pd.read_sql_query(
            "SELECT task_name, subject, deadline, status, created_at FROM tasks WHERE user_id=? ORDER BY deadline",
            conn,
            params=(uid,),
        )
    if dataset == "schedules":
        return pd.read_sql_query(
            "SELECT date, subject, study_hours, completed FROM schedules WHERE user_id=? ORDER BY date",
            conn,
            params=(uid,),
        )

    return pd.read_sql_query(
        """SELECT date, ROUND(COALESCE(SUM(hours),0),2) AS total_hours
           FROM study_sessions WHERE user_id=?
           GROUP BY date ORDER BY date""",
        conn,
        params=(uid,),
    )


@app.route("/analytics/export/backup/all")
@login_required
def export_backup_zip():
    """Download one ZIP containing all analytics CSV exports."""
    uid = session["user_id"]
    conn = get_db()

    datasets = [
        ("daily", "daily_hours.csv"),
        ("sessions", "study_sessions.csv"),
        ("tasks", "tasks.csv"),
        ("schedules", "schedules.csv"),
    ]

    zip_buffer = io.BytesIO()
    with zipfile.ZipFile(zip_buffer, mode="w", compression=zipfile.ZIP_DEFLATED) as zf:
        for dataset, filename in datasets:
            df = _build_export_dataframe(uid, dataset, conn)
            zf.writestr(filename, df.to_csv(index=False))

    conn.close()
    zip_buffer.seek(0)

    response = make_response(zip_buffer.getvalue())
    response.headers["Content-Disposition"] = (
        f"attachment; filename=backup_user_{uid}_{date.today().strftime('%Y%m%d')}.zip"
    )
    response.mimetype = "application/zip"
    return response


@app.route("/analytics/export/<string:dataset>")
@login_required
def export_analytics_csv(dataset):
    """Download analytics-related user data as CSV (sessions/tasks/schedules/daily)."""
    uid = session["user_id"]
    allowed = {"sessions", "tasks", "schedules", "daily"}
    if dataset not in allowed:
        return jsonify({"status": "error", "message": "Invalid dataset"}), 400

    conn = get_db()
    df = _build_export_dataframe(uid, dataset, conn)
    conn.close()

    csv_data = df.to_csv(index=False)
    response = make_response(csv_data)
    response.headers["Content-Disposition"] = (
        f"attachment; filename={dataset}_user_{uid}_{date.today().strftime('%Y%m%d')}.csv"
    )
    response.mimetype = "text/csv"
    return response


@app.route('/settings', methods=['GET', 'POST'])
@login_required
def settings():
    uid = session['user_id']
    conn = get_db()
    if request.method == 'POST':
        try:
            val = float(request.form.get('daily_limit', '6').strip())
            if val < 0:
                raise ValueError('Must be non-negative')
        except Exception:
            flash('Please enter a valid number for daily hours.', 'danger')
            conn.close()
            return redirect(url_for('settings'))

        # Read timer settings (integers)
        try:
            fmins = int(request.form.get('focus_minutes', '').strip() or 25)
            smins = int(request.form.get('short_minutes', '').strip() or 5)
            lmins = int(request.form.get('long_minutes', '').strip() or 15)
            sbefore = int(request.form.get('sessions_before_long', '').strip() or 4)
            if fmins < 1 or smins < 1 or lmins < 1 or sbefore < 1:
                raise ValueError('Values must be >= 1')
        except Exception:
            flash('Please enter valid integer values for timer minutes/sessions.', 'danger')
            conn.close()
            return redirect(url_for('settings'))

        try:
            conn.execute(
                'UPDATE users SET daily_hours_allowed = ?, timer_focus = ?, timer_short = ?, timer_long = ?, timer_sessions_before_long = ? WHERE id = ?',
                (val, fmins, smins, lmins, sbefore, uid),
            )
            conn.commit()
            flash('Settings saved.', 'success')
        except sqlite3.Error as e:
            flash(f'Failed to save settings: {e}', 'danger')
        finally:
            conn.close()
        return redirect(url_for('settings'))

    # GET - show current values (daily + timer)
    try:
        row = conn.execute(
            'SELECT COALESCE(daily_hours_allowed,6.0) AS daily, COALESCE(timer_focus,25) AS tf, COALESCE(timer_short,5) AS ts, COALESCE(timer_long,15) AS tl, COALESCE(timer_sessions_before_long,4) AS tss FROM users WHERE id=?',
            (uid,),
        ).fetchone()
        if row:
            daily_limit = round(float(row['daily']), 1)
            tf = int(row['tf'])
            ts = int(row['ts'])
            tl = int(row['tl'])
            tss = int(row['tss'])
        else:
            daily_limit, tf, ts, tl, tss = 6.0, 25, 5, 15, 4
    except Exception:
        daily_limit, tf, ts, tl, tss = 6.0, 25, 5, 15, 4
    conn.close()
    return render_template('settings.html', daily_limit=daily_limit, timer_focus=tf, timer_short=ts, timer_long=tl, timer_sessions_before_long=tss)


@app.route('/forgot', methods=['GET', 'POST'])
def forgot():
    if request.method == 'POST':
        email = request.form.get('email', '').strip()
        if not email:
            flash('Enter your email.', 'danger')
            return redirect(url_for('forgot'))
        conn = get_db()
        user = conn.execute('SELECT id, email, name FROM users WHERE email=?', (email,)).fetchone()
        if not user:
            flash('If that email exists, a reset link has been sent.', 'info')
            return redirect(url_for('login'))

        token = secrets.token_urlsafe(32)
        expires = (datetime.utcnow() + timedelta(hours=1)).strftime('%Y-%m-%d %H:%M:%S')
        conn.execute('INSERT INTO password_resets (user_id, token, expires_at) VALUES (?,?,?)', (user['id'], token, expires))
        conn.commit()
        conn.close()

        reset_link = url_for('reset_password', token=token, _external=True)

        # Try to send email if SMTP configured
        smtp_host = os.environ.get('SMTP_HOST')
        smtp_port = int(os.environ.get('SMTP_PORT', '0') or 0)
        smtp_user = os.environ.get('SMTP_USER')
        smtp_pass = os.environ.get('SMTP_PASS')
        from_addr = os.environ.get('FROM_EMAIL', smtp_user)
        try:
            if smtp_host and smtp_port and smtp_user and smtp_pass and from_addr:
                msg = EmailMessage()
                msg['Subject'] = 'AI Study Planner — Password reset'
                msg['From'] = from_addr
                msg['To'] = user['email']
                msg.set_content(f"Hi {user['name']},\n\nUse this link to reset your password (expires in 1 hour):\n{reset_link}\n\nIf you didn't request this, ignore.\n")
                with smtplib.SMTP(smtp_host, smtp_port, timeout=10) as s:
                    s.starttls()
                    s.login(smtp_user, smtp_pass)
                    s.send_message(msg)
                flash('Reset link sent to your email.', 'success')
            else:
                # SMTP not configured — show link in flash (development)
                flash(f'Reset link (dev): {reset_link}', 'info')
        except Exception:
            flash(f'Reset link (dev): {reset_link}', 'info')

        return redirect(url_for('login'))

    return render_template('forgot.html')


@app.route('/reset/<token>', methods=['GET', 'POST'])
def reset_password(token):
    conn = get_db()
    row = conn.execute('SELECT * FROM password_resets WHERE token=?', (token,)).fetchone()
    if not row:
        flash('Invalid or expired reset token.', 'danger')
        return redirect(url_for('login'))

    # check expiry
    expires = datetime.strptime(row['expires_at'], '%Y-%m-%d %H:%M:%S')
    if datetime.utcnow() > expires:
        conn.execute('DELETE FROM password_resets WHERE id=?', (row['id'],))
        conn.commit()
        conn.close()
        flash('Reset token expired.', 'danger')
        return redirect(url_for('forgot'))

    if request.method == 'POST':
        new = request.form.get('new_password', '')
        confirm = request.form.get('confirm_password', '')
        if not new or len(new) < 6:
            flash('Password must be at least 6 characters.', 'danger')
            return redirect(url_for('reset_password', token=token))
        if new != confirm:
            flash('Passwords do not match.', 'danger')
            return redirect(url_for('reset_password', token=token))

        # update password
        conn.execute('UPDATE users SET password=? WHERE id=?', (generate_password_hash(new), row['user_id']))
        conn.execute('DELETE FROM password_resets WHERE id=?', (row['id'],))
        conn.commit()
        conn.close()
        flash('Password updated. Please log in.', 'success')
        return redirect(url_for('login'))

    conn.close()
    return render_template('reset_password.html')


@app.route('/profile', methods=['GET', 'POST'])
@login_required
def profile():
    uid = session['user_id']
    conn = get_db()

    if request.method == 'POST':
        # Distinguish form actions by hidden field 'action'
        action = request.form.get('action', '')
        if action == 'update_profile':
            name = request.form.get('name', '').strip()
            class_name = request.form.get('class_name', '').strip()
            age = request.form.get('age', '').strip()
            daily_hours = request.form.get('daily_hours')
            receive_emails = 1 if request.form.get('receive_emails') == 'on' else 0
            try:
                age_val = int(age) if age else None
            except ValueError:
                age_val = None

            try:
                daily_hours_val = float(daily_hours) if daily_hours else None
            except Exception:
                daily_hours_val = None

            # Handle avatar upload
            avatar_file = request.files.get('avatar')
            avatar_filename = None
            if avatar_file and avatar_file.filename:
                fname = secure_filename(avatar_file.filename)
                avatar_filename = f"{uid}_{secrets.token_hex(8)}_{fname}"
                avatar_path = os.path.join(UPLOAD_FOLDER, avatar_filename)
                avatar_file.save(avatar_path)

            if not name:
                flash('Name cannot be empty.', 'danger')
                return redirect(url_for('profile'))

            # Build update tuple
            if avatar_filename:
                conn.execute("UPDATE users SET name=?, class_name=?, age=?, avatar=?, receive_emails=?, daily_hours_allowed=? WHERE id=?",
                             (name, class_name, age_val, avatar_filename, receive_emails, daily_hours_val, uid))
                session['user_avatar'] = avatar_filename
            else:
                conn.execute("UPDATE users SET name=?, class_name=?, age=?, receive_emails=?, daily_hours_allowed=? WHERE id=?",
                             (name, class_name, age_val, receive_emails, daily_hours_val, uid))
            conn.commit()
            session['user_name'] = name
            flash('Profile updated.', 'success')
            return redirect(url_for('profile'))

        if action == 'change_password':
            current = request.form.get('current_password', '')
            new = request.form.get('new_password', '')
            confirm = request.form.get('confirm_password', '')
            if not new or len(new) < 6:
                flash('New password must be at least 6 characters.', 'danger')
                return redirect(url_for('profile'))
            if new != confirm:
                flash('New password and confirmation do not match.', 'danger')
                return redirect(url_for('profile'))

            user = conn.execute('SELECT password FROM users WHERE id=?', (uid,)).fetchone()
            if not user or not check_password_hash(user['password'], current):
                flash('Current password is incorrect.', 'danger')
                return redirect(url_for('profile'))

            conn.execute('UPDATE users SET password=? WHERE id=?', (generate_password_hash(new), uid))
            conn.commit()
            flash('Password changed.', 'success')
            return redirect(url_for('profile'))

    # GET: render profile form
    row = conn.execute('SELECT id, name, email, class_name, age, avatar, receive_emails, daily_hours_allowed FROM users WHERE id=?', (uid,)).fetchone()
    conn.close()
    user = dict(row) if row else {}
    return render_template('profile.html', user=user)


@app.route("/quiz", methods=["GET", "POST"])
@login_required
def quiz():
    quiz_questions = None
    quiz_results = None
    score = None
    total = 0
    source_name = None
    attempt_id = None
    quiz_history = _fetch_quiz_attempts(session["user_id"])

    if request.method == "POST":
        action = request.form.get("action", "generate")

        if action == "generate":
            pdf_file = request.files.get("quiz_pdf")
            if not pdf_file or not pdf_file.filename:
                flash("Please choose a PDF file to generate a quiz.", "warning")
                return render_template("quiz.html")

            if not pdf_file.filename.lower().endswith(".pdf"):
                flash("Only PDF files are supported.", "danger")
                return render_template("quiz.html")

            try:
                extracted_text = _extract_pdf_text(pdf_file)
            except Exception as exc:
                flash(f"Could not read the PDF: {exc}", "danger")
                return render_template("quiz.html")

            quiz_questions = _build_quiz_questions(extracted_text)
            source_name = secure_filename(pdf_file.filename)

            if not quiz_questions:
                flash("No quiz questions could be generated from that PDF. Try a more text-heavy file.", "warning")
                return render_template("quiz.html", source_name=source_name, quiz_history=quiz_history)

            flash(f"Generated {len(quiz_questions)} quiz question(s) from {source_name}.", "success")
            return render_template(
                "quiz.html",
                quiz_questions=quiz_questions,
                source_name=source_name,
                quiz_history=quiz_history,
            )

        if action == "grade":
            quiz_data_raw = request.form.get("quiz_data", "[]")
            source_name = request.form.get("source_name", "").strip()
            try:
                quiz_questions = json.loads(quiz_data_raw)
            except json.JSONDecodeError:
                flash("Quiz data could not be loaded. Please generate the quiz again.", "danger")
                return redirect(url_for("quiz"))

            if not isinstance(quiz_questions, list) or not quiz_questions:
                flash("Quiz data is missing. Please generate the quiz again.", "danger")
                return redirect(url_for("quiz"))

            quiz_results = []
            correct_count = 0
            total = len(quiz_questions)

            for index, question in enumerate(quiz_questions):
                selected = request.form.get(f"answer_{index}", "")
                correct_answer = str(question.get("answer", "")).strip()
                is_correct = selected.strip().lower() == correct_answer.lower()
                if is_correct:
                    correct_count += 1

                quiz_results.append({
                    "question": question.get("question", ""),
                    "selected": selected,
                    "correct": correct_answer,
                    "is_correct": is_correct,
                })

            score = round((correct_count / total) * 100) if total else 0

            quiz_results_payload = json.dumps(quiz_results)
            quiz_data_payload = json.dumps(quiz_questions)
            conn = get_db()
            cursor = conn.execute(
                """
                INSERT INTO quiz_attempts (
                    user_id, source_name, total_questions, correct_answers, score,
                    quiz_data, quiz_results
                ) VALUES (?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    session["user_id"],
                    source_name,
                    total,
                    correct_count,
                    score,
                    quiz_data_payload,
                    quiz_results_payload,
                ),
            )
            attempt_id = cursor.lastrowid
            conn.commit()
            conn.close()

            quiz_history = _fetch_quiz_attempts(session["user_id"])
            flash(f"You scored {correct_count}/{total} ({score}%).", "info")

            return render_template(
                "quiz.html",
                quiz_questions=quiz_questions,
                quiz_results=quiz_results,
                score=score,
                total=total,
                attempt_id=attempt_id,
                source_name=source_name,
                quiz_history=quiz_history,
            )

        if action == "export":
            source_name = request.form.get("source_name", "").strip()
            quiz_data_raw = request.form.get("quiz_data", "[]")
            try:
                quiz_questions = json.loads(quiz_data_raw)
            except json.JSONDecodeError:
                flash("Quiz data could not be exported. Generate the quiz again.", "danger")
                return redirect(url_for("quiz"))

            if not isinstance(quiz_questions, list) or not quiz_questions:
                flash("Quiz data is missing. Generate the quiz again.", "danger")
                return redirect(url_for("quiz"))

            pdf_bytes = _build_quiz_pdf_bytes(
                title="AI Study Planner Quiz Export",
                quiz_questions=quiz_questions,
                source_name=source_name,
            )
            filename = f"quiz_export_{datetime.now().strftime('%Y%m%d_%H%M%S')}.pdf"
            return _quiz_pdf_response(filename, pdf_bytes)

        flash("Unsupported quiz action.", "danger")

    return render_template("quiz.html", quiz_history=quiz_history)


@app.route("/codequest")
@login_required
def codequest():
    return render_template("codequest.html")


@app.route("/codequest/raw")
@login_required
def codequest_raw():
    return send_from_directory(BASE_DIR, "codequest.html")


@app.route("/quiz/export/<int:attempt_id>")
@login_required
def quiz_export_attempt(attempt_id):
    conn = get_db()
    attempt = conn.execute(
        """
        SELECT id, user_id, source_name, total_questions, correct_answers, score,
               quiz_data, quiz_results, created_at
        FROM quiz_attempts
        WHERE id = ? AND user_id = ?
        """,
        (attempt_id, session["user_id"]),
    ).fetchone()
    conn.close()

    if not attempt:
        flash("Quiz attempt not found.", "danger")
        return redirect(url_for("quiz"))

    quiz_questions = json.loads(attempt["quiz_data"])
    quiz_results = json.loads(attempt["quiz_results"])
    pdf_bytes = _build_quiz_pdf_bytes(
        title="AI Study Planner Quiz Attempt",
        quiz_questions=quiz_questions,
        source_name=attempt["source_name"],
        attempt=attempt,
        quiz_results=quiz_results,
    )
    filename = f"quiz_attempt_{attempt_id}.pdf"
    return _quiz_pdf_response(filename, pdf_bytes)


@app.route("/api/reminders")
@login_required
def api_reminders():
    uid       = session["user_id"]
    today     = date.today()
    today_str = today.strftime("%Y-%m-%d")
    conn      = get_db()

    tasks_due = conn.execute(
        """SELECT task_name, subject, deadline FROM tasks
           WHERE user_id=? AND status='Pending'
           AND deadline >= ? AND deadline <= date(?, '+3 days')
           ORDER BY deadline""",
        (uid, today_str, today_str),
    ).fetchall()

    sessions_today = conn.execute(
        "SELECT subject, study_hours FROM schedules WHERE user_id=? AND date=? AND completed=0",
        (uid, today_str),
    ).fetchall()

    conn.close()

    msgs = []
    for t in tasks_due:
        days_left = (datetime.strptime(t["deadline"], "%Y-%m-%d").date() - today).days
        if days_left == 0:
            msgs.append(f"⚠️ Due TODAY: {t['task_name']} ({t['subject']})")
        elif days_left == 1:
            msgs.append(f"🔴 Due tomorrow: {t['task_name']} ({t['subject']})")
        else:
            msgs.append(f"📅 Due in {days_left} days: {t['task_name']} ({t['subject']})")

    for s in sessions_today:
        msgs.append(f"📚 Study today: {s['subject']} — {s['study_hours']}h scheduled")

    return jsonify({"reminders": msgs})


# ── Entry point ───────────────────────────────────────────────────────────────
if __name__ == "__main__":
    host = "0.0.0.0"
    port = int(os.environ.get("PORT", 5000))
    debug_mode = not _is_hosted_runtime() and os.environ.get("FLASK_DEBUG", "1") != "0"
    local_url = f"http://127.0.0.1:{port}"

    # Attempt to determine a LAN-accessible IP address for network URL
    network_url = None
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]
        s.close()
        if ip and not ip.startswith("127."):
            network_url = f"http://{ip}:{port}"
    except Exception:
        network_url = None

    # Build a neat dynamic box based on content width
    lines = ["AI Study Planner & Productivity Coach", "", f"Local:   {local_url}"]
    if network_url:
        lines.append(f"Network: {network_url}")
    lines.append("")
    lines.append("Press Ctrl+C to stop")

    inner_width = max(len(l) for l in lines) + 2
    print("╔" + "═" * inner_width + "╗")
    for l in lines:
        print("║ " + l.ljust(inner_width - 1) + "║")
    print("╚" + "═" * inner_width + "╝")

    # Open the browser once when the reloader child process runs (avoids double-open)
    if not _is_hosted_runtime() and os.environ.get("WERKZEUG_RUN_MAIN") == "true":
        try:
            webbrowser.open_new_tab(local_url)
        except Exception:
            pass

    app.run(debug=debug_mode, host=host, port=port)
