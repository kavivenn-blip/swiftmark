// swiftmark — a fast drop-in replacement for marked 18.1.3 (default options).
// parse(markdown) returns exactly the HTML marked.parse(markdown) returns,
// for every string. Written from the CommonMark 0.31.2 + GFM 0.29 specs and
// black-box probing of marked's behaviour; no marked code is used here.
//
// Design: single-pass block parser (spec appendix A algorithm, with
// column-aware tab handling) over pre-split lines, then a single-pass inline
// parser with a delimiter stack. Rendering is fused into parsing wherever
// possible; output is built as an array of string chunks joined once.

const SP = 32, TAB = 9, NL = 10, BANG = 33, QUOT = 34, HASH = 35, DOLLAR = 36,
  PCT = 37, AMP = 38, APOS = 39, LPAREN = 40, RPAREN = 41, STAR = 42, PLUS = 43,
  COMMA = 44, MINUS = 45, DOT = 46, SLASH = 47, COLON = 58, SEMI = 59, LT = 60,
  EQ = 61, GT = 62, Q = 63, AT = 64, LB = 91, BSLASH = 92, RB = 93, CARET = 94,
  UNDER = 95, BTICK = 96, LBRACE = 123, PIPE = 124, RBRACE = 125, TILDE = 126,
  LBRACK = 91, RBRACK = 93, UNDERSCORE = 95, BACKTICK = 96, BACKSLASH = 92,
  LF = 10, SQUOT = 39;

// ---- character classes (ASCII fast paths; non-ASCII is never punctuation) ----
function isAlpha(c) { return (c >= 65 && c <= 90) || (c >= 97 && c <= 122); }
function isDigit(c) { return c >= 48 && c <= 57; }
function isAlnum(c) { return isAlpha(c) || isDigit(c); }
function isSpace(c) { return c === SP || c === TAB || c === NL; }
// CommonMark whitespace: space, tab, LF, VT(11), FF(12), CR(13). CR is
// normalized away before parsing, so only these remain.
function isWs(c) { return c === SP || c === TAB || c === NL || c === 11 || c === 12; }
function isPunct(c) {
  return (c >= 33 && c <= 47) || (c >= 58 && c <= 64) ||
    (c >= 91 && c <= 96) || (c >= 123 && c <= 126);
}
// Unicode whitespace (for flanking checks): use a small regex-free test on
// the common cases; fall back to a RegExp test for the rest.
const WS_RE = /\s/;
function isUniWs(c) {
  return c === SP || c === TAB || c === NL || c === 11 || c === 12 || c === 13 ||
    (c > 127 && WS_RE.test(String.fromCharCode(c)));
}
function isUniPunct(c) {
  if (c < 128) return isPunct(c);
  // CommonMark "Unicode punctuation" = general categories P or S
  return /[\p{P}\p{S}]/u.test(String.fromCharCode(c));
}

// ---- HTML escaping ----
// marked's escape(html, encode): with encode=false, & is escaped only when
// NOT followed by a valid entity-looking tail (#digits; | #x hex; | word;).
// < > " ' are always escaped. With encode=true, & is always escaped.
// Numeric entities are decoded by the caller before escaping, and named
// entities are left untouched (marked 18 does not decode named entities).
function escapeHtml(s, encode) {
  let out = '';
  let start = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    let rep = null;
    if (c === 38) { // &
      if (encode) rep = '&amp;';
      else {
        // lookahead: #digits; | #x hex; | #X hex; | word;
        let j = i + 1;
        if (s.charCodeAt(j) === 35) { // #
          j++;
          let ok = false;
          if (s.charCodeAt(j) === 120 || s.charCodeAt(j) === 88) { // x X
            j++;
            const h0 = j;
            while (isHex(s.charCodeAt(j))) j++;
            if (j > h0 && s.charCodeAt(j) === 59) ok = true;
          } else {
            const d0 = j;
            while (isDigit(s.charCodeAt(j))) j++;
            if (j > d0 && s.charCodeAt(j) === 59) ok = true;
          }
          if (!ok) rep = '&amp;';
        } else {
          const w0 = j;
          while (isAlnum(s.charCodeAt(j))) j++;
          if (!(j > w0 && s.charCodeAt(j) === 59)) rep = '&amp;';
        }
      }
    } else if (c === 60) rep = '&lt;';
    else if (c === 62) rep = '&gt;';
    else if (c === 34) rep = '&quot;';
    else if (c === 39) rep = '&#39;';
    if (rep !== null) {
      out += s.slice(start, i) + rep;
      start = i + 1;
    }
  }
  return start === 0 ? s : out + s.slice(start);
}
function isHex(c) {
  return (c >= 48 && c <= 57) || (c >= 65 && c <= 70) || (c >= 97 && c <= 102);
}

// Decode a numeric entity starting at s[i] === '&' (already known to be
// '&#...;'). Returns {ch, next} or null if not a valid numeric entity.
// Valid: &#1-7 digits; and &#x / &#X 1-6 hex digits; value 0, surrogate or
// > 0x10FFFF decodes to U+FFFD.
function decodeNumericEntity(s, i) {
  let j = i + 2; // past '&#'
  let code = 0;
  if (s.charCodeAt(j) === 120 || s.charCodeAt(j) === 88) { // x X
    j++;
    const start = j;
    while (isHex(s.charCodeAt(j))) {
      const c = s.charCodeAt(j);
      code = code * 16 + (c <= 57 ? c - 48 : (c <= 70 ? c - 55 : c - 87));
      if (j - start > 6) return null;
      j++;
    }
    if (j === start || j - start > 6 || s.charCodeAt(j) !== 59) return null;
  } else {
    const start = j;
    while (isDigit(s.charCodeAt(j))) {
      code = code * 10 + (s.charCodeAt(j) - 48);
      if (j - start > 7) return null;
      j++;
    }
    if (j === start || j - start > 7 || s.charCodeAt(j) !== 59) return null;
  }
  if (code === 0 || code > 0x10ffff || (code >= 0xd800 && code <= 0xdfff)) code = 0xfffd;
  return { ch: String.fromCodePoint(code), next: j + 1 };
}

// marked's cleanUrl: encodeURI, then un-escape %25 back to %.
// (encodeURI leaves % alone, so the %25 fix only fires for a literal %25
// that encodeURI itself produced from a '%' in the input.)
function cleanUrl(href) {
  try {
    href = encodeURI(href).replace(/%25/g, '%');
  } catch (e) {
    return null;
  }
  return href;
}

// Normalize a link label for reference lookup: collapse whitespace runs to
// a single space, trim, case-fold (Unicode-aware lower case).
function normalizeLabel(s) {
  // Unicode case folding: ß/ẞ fold to "ss" (toLowerCase alone gives ß)
  return s.replace(/\s+/g, ' ').trim().toLowerCase().replace(/ß/g, 'ss');
}

// ---- link destination / title parsing (shared by inline links and defs) ----
// Parse a link destination starting at s[i] (i points at '<' or a non-space
// char). Returns {dest, next} where next is the index just past the dest,
// or null. Backslash escapes and numeric entities are NOT decoded here:
// marked keeps the raw text and only encodeURI's it later.
function parseDest(s, i) {
  const n = s.length;
  if (s.charCodeAt(i) === LT) {
    // <...> destination: no unescaped < or newline; backslash escapes ok.
    let j = i + 1;
    let dest = '';
    while (j < n) {
      const c = s.charCodeAt(j);
      if (c === NL) return null;
      if (c === LT) return null;
      if (c === GT) return { dest, next: j + 1 };
      if (c === BSLASH && j + 1 < n && isPunct(s.charCodeAt(j + 1))) {
        dest += s[j + 1];
        j += 2;
      } else {
        dest += s[j];
        j++;
      }
    }
    return null;
  }
  // bare destination: balanced parens, no spaces/control chars.
  let j = i;
  let depth = 0;
  let dest = '';
  while (j < n) {
    const c = s.charCodeAt(j);
    if (isSpace(c) || c < 32) break;
    if (c === LPAREN) {
      depth++;
      if (depth > 32) return null;
      dest += s[j];
      j++;
    } else if (c === RPAREN) {
      if (depth === 0) break;
      depth--;
      dest += s[j];
      j++;
    } else if (c === BSLASH && j + 1 < n && isPunct(s.charCodeAt(j + 1))) {
      dest += s[j + 1];
      j += 2;
    } else {
      dest += s[j];
      j++;
    }
  }
  if (dest.length === 0) return null;
  return { dest, next: j };
}

// Parse a link title starting at s[i] (after skipping spaces/tabs/newlines
// is the caller's job; here i points at ", ' or (). Returns {title, next}.
function parseTitle(s, i) {
  const n = s.length;
  const c = s.charCodeAt(i);
  if (c === QUOT || c === APOS) {
    const q = c;
    let j = i + 1;
    let title = '';
    while (j < n) {
      const ch = s.charCodeAt(j);
      if (ch === q) return { title, next: j + 1 };
      if (ch === NL) {
        // a title in quotes may span lines only if the closing quote is on
        // the same "paragraph" — marked allows newlines inside titles.
        title += s[j];
        j++;
      } else if (ch === BSLASH && j + 1 < n && isPunct(s.charCodeAt(j + 1))) {
        title += s[j + 1];
        j += 2;
      } else {
        title += s[j];
        j++;
      }
    }
    return null;
  }
  if (c === LPAREN) {
    let j = i + 1;
    let title = '';
    while (j < n) {
      const ch = s.charCodeAt(j);
      if (ch === RPAREN) return { title, next: j + 1 };
      if (ch === LPAREN) return null;
      if (ch === BSLASH && j + 1 < n && isPunct(s.charCodeAt(j + 1))) {
        title += s[j + 1];
        j += 2;
      } else {
        title += s[j];
        j++;
      }
    }
    return null;
  }
  return null;
}

// ---- block parsing ----
// Line cursor: tracks position (char index), visual column, and a partially
// consumed tab (its remaining width in spaces). Tabs expand to the next
// multiple of 4 for structure; a tab that is only partly consumed for
// indentation contributes its remaining width as spaces to the content.
function makeLine() {
  return { s: '', len: 0, pos: 0, col: 0, ptab: 0, indent: 0, blank: false };
}
function lineReset(L, s) {
  L.s = s; L.len = s.length; L.pos = 0; L.col = 0; L.ptab = 0; L.indent = 0; L.blank = false;
}
function peek(L) {
  if (L.ptab > 0) return SP;
  return L.pos < L.len ? L.s.charCodeAt(L.pos) : -1;
}
function peekAt(L, off) {
  const p = L.pos + off;
  return p < L.len ? L.s.charCodeAt(p) : -1;
}
// Advance the cursor by n visual columns, consuming chars (a tab that would
// overshoot is left in place with its remainder recorded in ptab).
function advance(L, n) {
  while (n > 0) {
    if (L.pos >= L.len) { L.col += n; n = 0; break; }
    const c = L.s.charCodeAt(L.pos);
    if (c === TAB) {
      if (L.ptab > 0) {
        if (n < L.ptab) { L.ptab -= n; L.col += n; n = 0; }
        else { n -= L.ptab; L.col += L.ptab; L.pos++; L.ptab = 0; }
      } else {
        const w = 4 - (L.col % 4);
        if (n < w) { L.ptab = w - n; L.col += n; n = 0; }
        else { n -= w; L.col += w; L.pos++; }
      }
    } else {
      L.pos++; L.col++; n--;
    }
  }
}
// Measure leading whitespace from the current position without moving it.
// Returns {indent, blank, pos, col, ptab} at the first non-space char.
function measureIndent(L) {
  let pos = L.pos, col = L.col, ptab = L.ptab, indent = 0;
  while (true) {
    if (pos >= L.len) return { indent, blank: true, pos, col, ptab };
    const c = L.s.charCodeAt(pos);
    if (c === SP) { pos++; col++; indent++; ptab = 0; }
    else if (c === TAB) {
      if (ptab > 0) {
        indent++; col++;
        if (ptab === 1) { pos++; ptab = 0; } else ptab--;
      } else {
        const w = 4 - (col % 4);
        indent++; col++;
        if (w === 1) { pos++; } else ptab = w - 1;
      }
    } else return { indent, blank: false, pos, col, ptab };
  }
}
// Commit the cursor to the position just after the leading whitespace.
function scanIndent(L) {
  const m = measureIndent(L);
  L.pos = m.pos; L.col = m.col; L.ptab = m.ptab; L.indent = m.indent; L.blank = m.blank;
  return m;
}
// The rest of the line from the cursor, with a partially consumed tab
// expanded to its remaining spaces.
function lineContent(L) {
  if (L.ptab > 0) return ' '.repeat(L.ptab) + L.s.slice(L.pos + 1);
  return L.s.slice(L.pos);
}
// Expand a leading tab of a code-content line to spaces when a container
// indent was consumed (L.col > 0); at column 0 the tab is kept literally.
// (lineContent already expands a partially consumed tab via L.ptab.)
function expandCodeTab(s, L) {
  if (L.ptab === 0 && s.charCodeAt(0) === TAB && L.col > 0) {
    return ' '.repeat(4 - (L.col % 4)) + s.slice(1);
  }
  return s;
}
// The rest of the line, trimmed of trailing spaces/tabs (for leaf starts).
function lineContentTrimmed(L) {
  let s = lineContent(L);
  let e = s.length;
  while (e > 0 && (s.charCodeAt(e - 1) === SP || s.charCodeAt(e - 1) === TAB)) e--;
  return s.slice(0, e);
}

// Block node types: doc, bq, list, item, p, h, code (fenced), icode, html,
// hr, table. Containers and leaves carry `open`; leaves carry `lines` or
// inline source; lists carry tight/loose; items carry markerOff/pad.
function newNode(t) {
  return { t, children: [], open: true, lines: null, parent: null };
}
function addChild(parent, node) {
  node.parent = parent;
  parent.children.push(node);
  return node;
}
function tipOf(root) {
  let n = root;
  while (n.children.length) {
    const last = n.children[n.children.length - 1];
    if (!last.open) break;
    n = last;
  }
  return n;
}
// The deepest last leaf block under node (following last children).
function lastLeaf(node) {
  let n = node;
  while (n.children && n.children.length) n = n.children[n.children.length - 1];
  return n;
}
// A type 1-5 HTML block followed by a blank line loses its trailing
// newline. Called when a blank line is seen.
function stripHtmlTrailingNl(root) {
  const n = lastLeaf(root);
  if (n.t === 'html' && n.htmlType <= 5 && n.src && n.src.charCodeAt(n.src.length - 1) === NL) {
    n.src = n.src.slice(0, -1);
  }
}
// Close (finalize) a block and everything below it. `defs` collects link
// reference definitions; paragraphs that turn out to hold only definitions
// are removed from their parent.
function finalize(node, defs) {
  node.open = false;
  if (node.t === 'p') {
    const src = node.lines.join('\n');
    const res = extractDefs(src, defs);
    if (res.text.length === 0) {
      // paragraph held only definitions: drop it
      const p = node.parent;
      const i = p.children.indexOf(node);
      if (i >= 0) p.children.splice(i, 1);
      node.src = '';
    } else {
      node.src = res.text;
    }
    node.lines = null;
  } else if (node.t === 'code' || node.t === 'icode' || node.t === 'html') {
    // strip trailing blank lines, then join with a newline each
    const ls = node.lines;
    if (node.t === 'icode') {
      while (ls.length && ls[ls.length - 1] === '') ls.pop();
    } else if (node.t === 'code') {
      // a fenced block loses exactly one trailing blank line
      if (ls.length && ls[ls.length - 1] === '') ls.pop();
    } else {
      while (ls.length && ls[ls.length - 1] === '') ls.pop();
    }
    if (node.t === 'html') {
      // Types 1-5 end on an end marker and keep the trailing newline of
      // the end-marker line (unless a blank line follows — handled by
      // the blank-line branch stripping it). Types 6-7 keep a trailing
      // newline only when the block is the last block in the document
      // (added by parse()).
      node.src = ls.join('\n');
      if (node.htmlType <= 5) node.src = ls.length ? node.src + '\n' : '';
    } else {
      node.src = ls.length ? ls.join('\n') + '\n' : '';
    }
    node.lines = null;
  }
}
function closeTo(root, container, defs) {
  // finalize every open block strictly below `container`
  let n = tipOf(root);
  while (n !== container) {
    finalize(n, defs);
    n = n.parent;
  }
}

// ---- link reference definitions ----
// Parse as many leading definitions as possible from a paragraph's source.
// A definition: [label]: <ws?> dest <ws?> [title] <ws?> EOL. Whitespace
// between parts may include a single newline. Returns {text, defs} where
// text is the remaining paragraph text (possibly '').
function extractDefs(src, defs) {
  let i = 0;
  const n = src.length;
  while (true) {
    // skip up to 3 leading spaces (and tabs count as columns)
    let j = i, col = 0;
    while (j < n && (src.charCodeAt(j) === SP || src.charCodeAt(j) === TAB)) {
      if (src.charCodeAt(j) === TAB) col += 4 - (col % 4); else col++;
      if (col > 3) break;
      j++;
    }
    if (col > 3 || src.charCodeAt(j) !== LB) break;
    const label = parseLabel(src, j);
    if (!label) break;
    let k = label.next;
    // ':'
    if (src.charCodeAt(k) !== COLON) break;
    k++;
    // whitespace (spaces/tabs, at most one newline)
    k = skipInlineWs(src, k, true);
    if (k === -1) break;
    const dest = parseDest(src, k);
    if (!dest) break;
    k = dest.next;
    // optional title, after whitespace (at most one newline). A title
    // must be preceded by whitespace: [foo]: <bar>(baz) is not a def.
    let title = null;
    let k2 = skipInlineWs(src, k, true);
    let kTitleEnd = -1;
    if (k2 !== -1 && k2 > k) {
      const t = parseTitle(src, k2);
      if (t) { title = t.title; kTitleEnd = t.next; }
    }
    // trailing spaces/tabs, then EOL or end. If a title parsed but junk
    // follows, the def is still valid with the destination alone — but
    // only when the destination itself is followed by EOL (i.e. the
    // title was on a later line); junk on the same line kills the def.
    let kEnd = kTitleEnd !== -1 ? kTitleEnd : k;
    let kCheck = kEnd;
    while (kCheck < n && (src.charCodeAt(kCheck) === SP || src.charCodeAt(kCheck) === TAB)) kCheck++;
    if (kCheck < n && src.charCodeAt(kCheck) !== NL) {
      if (kTitleEnd !== -1) {
        let kD = k;
        while (kD < n && (src.charCodeAt(kD) === SP || src.charCodeAt(kD) === TAB)) kD++;
        if (kD < n && src.charCodeAt(kD) !== NL) break;
        title = null;
        k = kD;
      } else {
        break;
      }
    } else {
      k = kCheck;
    }
    // a definition! record it (first one wins for a label). An empty
    // label is not a definition: leave the text in place (cm-552).
    // Labels are matched raw (no backslash unescaping): [Foo*bar\]] and
    // [Foo*bar]] share the raw label Foo*bar\] (cm-194), while [foo\!]
    // does not match [foo!] (cm-545).
    const key = normalizeLabel(label.text);
    if (key.length === 0) break;
    if (!defs.has(key)) {
      defs.set(key, { dest: dest.dest, title });
    }
    i = k < n ? k + 1 : k; // move past the newline
    if (i >= n) return { text: '' };
  }
  return { text: src.slice(i) };
}
// Skip spaces/tabs and at most one newline (plus following spaces/tabs).
// Returns the new index, or -1 if a blank line (two newlines) was hit.
function skipInlineWs(s, i, allowNewline) {
  const n = s.length;
  let seenNl = false;
  while (i < n) {
    const c = s.charCodeAt(i);
    if (c === SP || c === TAB) { i++; continue; }
    if (c === NL && allowNewline && !seenNl) { seenNl = true; i++; continue; }
    break;
  }
  if (i < n && s.charCodeAt(i) === NL && seenNl) return -1;
  return i;
}
// Parse a link label starting at s[i] === '['. Returns {text, next} where
// text is the raw label content (between brackets) and next is past ']',
// or null. The label ends at the FIRST unescaped ']' (no bracket-depth
// counting: an unescaped '[' inside a label makes it end early, so a
// following ':' is not found and the definition is invalid).
function parseLabel(s, i) {
  const n = s.length;
  let j = i + 1;
  let text = '';
  while (j < n) {
    const c = s.charCodeAt(j);
    if (c === BSLASH && j + 1 < n && isPunct(s.charCodeAt(j + 1))) {
      text += s[j] + s[j + 1];
      j += 2;
      continue;
    }
    if (c === RB) {
      if (text.length === 0 || text.length > 999) return null;
      return { text, next: j + 1 };
    }
    if (c === LB) return null; // an unescaped '[' is not allowed in a label
    if (c === NL) {
      // a label may span lines, but not a blank line
      if (j + 1 < n && s.charCodeAt(j + 1) === NL) return null;
      text += s[j];
      j++;
      continue;
    }
    text += s[j];
    j++;
  }
  return null;
}

// ---- HTML blocks ----
const BLOCK_TAGS = new Set(('address article aside base basefont blockquote body caption center col colgroup dd details dialog dir div dl dt fieldset figcaption figure footer form frame frameset h1 h2 h3 h4 h5 h6 head header hr html iframe legend li link main menu menuitem meta nav noframes ol optgroup option p param search section summary table tbody td tfoot th thead title tr track ul').split(' '));
const HTML_END1 = ['</script', '</pre', '</style', '</textarea'];
// Scan a tag starting at s[i] === '<'. Returns {name, isClose, end} with end
// just past the '>' (or -1 if the tag is not closed on this line).
function scanTag(s, i) {
  const n = s.length;
  let j = i + 1;
  let isClose = false;
  if (s.charCodeAt(j) === SLASH) { isClose = true; j++; }
  if (!isAlpha(s.charCodeAt(j))) return null;
  const n0 = j;
  j++;
  while (isAlnum(s.charCodeAt(j)) || s.charCodeAt(j) === MINUS) j++;
  const name = s.slice(n0, j).toLowerCase();
  if (isClose) {
    while (j < n && (s.charCodeAt(j) === SP || s.charCodeAt(j) === TAB)) j++;
    if (j < n && s.charCodeAt(j) === GT) return { name, isClose, end: j + 1 };
    return null;
  }
  // the tag name must be followed by whitespace, '>', '/' or end of line
  if (j < n) {
    const c = s.charCodeAt(j);
    if (!(c === SP || c === TAB || c === LF || c === GT || c === SLASH)) return null;
  }
  // open tag: parse attributes like scanInlineHtml does. Attributes must
  // be separated by whitespace.
  let firstAttr = true;
  let hadWs = false;
  for (;;) {
    while (j < n && (s.charCodeAt(j) === SP || s.charCodeAt(j) === TAB || s.charCodeAt(j) === LF)) { j++; hadWs = true; }
    if (j >= n) return null;
    const c = s.charCodeAt(j);
    if (c === GT) return { name, isClose, end: j + 1 };
    if (c === SLASH) {
      if (j + 1 < n && s.charCodeAt(j + 1) === GT) return { name, isClose, end: j + 2 };
      return null;
    }
    if (!firstAttr && !hadWs) return null; // attributes need whitespace
    firstAttr = false;
    hadWs = false;
    if (!(isAlpha(c) || c === UNDERSCORE || c === COLON)) return null;
    j++;
    while (j < n) {
      const ch = s.charCodeAt(j);
      if (isAlnum(ch) || ch === UNDERSCORE || ch === COLON || ch === DOT || ch === MINUS) j++;
      else break;
    }
    while (j < n && (s.charCodeAt(j) === SP || s.charCodeAt(j) === TAB || s.charCodeAt(j) === LF)) { j++; hadWs = true; }
    if (j < n && s.charCodeAt(j) === 61) { // '='
      j++;
      while (j < n && (s.charCodeAt(j) === SP || s.charCodeAt(j) === TAB || s.charCodeAt(j) === LF)) j++;
      if (j >= n) return null;
      const q = s.charCodeAt(j);
      if (q === QUOT || q === APOS) {
        j++;
        while (j < n && s.charCodeAt(j) !== q) j++;
        if (j >= n) return null;
        j++;
      } else {
        while (j < n) {
          const ch = s.charCodeAt(j);
          if (ch === SP || ch === TAB || ch === LF || ch === GT || ch === QUOT || ch === APOS || ch === 61 || ch === LT || ch === BTICK) break;
          j++;
        }
        if (j >= n) return null;
      }
      hadWs = false;
    }
  }
}
// Determine whether the line (from L's cursor, indent already measured,
// indent <= 3) starts an HTML block. Returns {type, end} where type is
// 1..7 and end is a string to look for (types 1-5) or '' for blank-line end
// (types 6-7); returns null if it does not start one. `inPara` is true
// when the tip is a paragraph (type 7 cannot interrupt one).
function htmlBlockStart(s, i, inPara) {
  const n = s.length;
  // skip up to 3 leading spaces
  let sp = 0;
  while (i < n && s.charCodeAt(i) === SP) { sp++; i++; }
  if (sp > 3) return null;
  if (s.charCodeAt(i) !== LT) return null;
  const c1 = s.charCodeAt(i + 1);
  const lower = s.slice(i, Math.min(n, i + 10)).toLowerCase();
  if (lower.startsWith('<!--')) return { type: 2, end: '-->' };
  if (lower.startsWith('<?')) return { type: 3, end: '?>' };
  if (lower.startsWith('<![cdata[')) return { type: 5, end: ']]>' };
  if (c1 === BANG && isAlpha(s.charCodeAt(i + 2))) return { type: 4, end: '>' };
  for (const tag of ['script', 'pre', 'style', 'textarea']) {
    if (lower.startsWith('<' + tag)) {
      const after = s.charCodeAt(i + 1 + tag.length);
      if (after === SP || after === TAB || after === GT || after === SLASH || i + 1 + tag.length >= n) {
        return { type: 1, end: HTML_END1 };
      }
    }
  }
  // type 6: < or </ followed by a block tag name (the tag need not close
  // on this line)
  {
    let j = i + 1;
    if (s.charCodeAt(j) === SLASH) j++;
    if (isAlpha(s.charCodeAt(j))) {
      const n0 = j;
      j++;
      while (isAlnum(s.charCodeAt(j)) || s.charCodeAt(j) === MINUS) j++;
      const name = s.slice(n0, j).toLowerCase();
      const c = s.charCodeAt(j);
      if (BLOCK_TAGS.has(name) && (c === SP || c === TAB || c === GT || c === SLASH || j >= n)) {
        return { type: 6, end: '' };
      }
    }
  }
  if (inPara) return null;
  // type 7: the line holds only this one tag (plus trailing whitespace)
  const tag = scanTag(s, i);
  if (!tag) return null;
  let k = tag.end;
  while (k < n && (s.charCodeAt(k) === SP || s.charCodeAt(k) === TAB)) k++;
  if (k >= n) return { type: 7, end: '' };
  return null;
}
function htmlBlockEnds(node, line) {
  const end = node.htmlEnd;
  if (typeof end === 'string') return line.toLowerCase().includes(end);
  for (const e of end) if (line.toLowerCase().includes(e)) return true;
  return false;
}

// ---- leaf start detectors (L's cursor is at the content start) ----
function isHrLine(s) {
  // ^ {0,3}([*_-])( *\1 *)*$ with at least 3 markers; s is already
  // indent-stripped by the caller (leading spaces removed) — but the
  // caller passes the line content from the cursor, so leading spaces
  // (up to 3) are part of it. We handle them here.
  let i = 0;
  const n = s.length;
  while (i < n && s.charCodeAt(i) === SP) i++;
  if (i > 3) return false;
  const c = s.charCodeAt(i);
  if (c !== STAR && c !== MINUS && c !== UNDER) return false;
  let count = 0;
  while (i < n) {
    const ch = s.charCodeAt(i);
    if (ch === c) { count++; i++; }
    else if (ch === SP || ch === TAB) i++;
    else return false;
  }
  return count >= 3;
}
// ATX heading: ^ {0,3}#{1,6}(?:[ \t]+(.*?)|[ \t]*)$ — returns {level, src}
// where src is the heading text (closing #'s removed). s is the line
// content from the cursor.
function tryAtx(s) {
  let i = 0;
  const n = s.length;
  while (i < n && s.charCodeAt(i) === SP) i++;
  if (i > 3) return null;
  let level = 0;
  while (i < n && s.charCodeAt(i) === HASH) { level++; i++; }
  if (level === 0 || level > 6) return null;
  // after the #'s: end of line, or space/tab
  if (i < n && s.charCodeAt(i) !== SP && s.charCodeAt(i) !== TAB) return null;
  let rest = s.slice(i);
  // trim trailing spaces/tabs, then a closing sequence of #'s preceded by
  // a space/tab (checked before stripping leading spaces, so that a rest
  // consisting only of #'s is recognised as a closing sequence)
  let e = rest.length;
  while (e > 0 && (rest.charCodeAt(e - 1) === SP || rest.charCodeAt(e - 1) === TAB)) e--;
  rest = rest.slice(0, e);
  let h = rest.length;
  while (h > 0 && rest.charCodeAt(h - 1) === HASH) h--;
  if (h < rest.length && h > 0 && (rest.charCodeAt(h - 1) === SP || rest.charCodeAt(h - 1) === TAB)) {
    rest = rest.slice(0, h);
    e = rest.length;
    while (e > 0 && (rest.charCodeAt(e - 1) === SP || rest.charCodeAt(e - 1) === TAB)) e--;
    rest = rest.slice(0, e);
  }
  // strip leading spaces/tabs
  let b = 0;
  while (b < rest.length && (rest.charCodeAt(b) === SP || rest.charCodeAt(b) === TAB)) b++;
  rest = rest.slice(b);
  return { level, src: rest };
}
// Fenced code: ^ {0,3}(`{3,}|~{3,})[^\n]*$ — returns {fence, flen, info}.
function tryFence(s) {
  let i = 0;
  const n = s.length;
  while (i < n && s.charCodeAt(i) === SP) i++;
  if (i > 3) return null;
  const c = s.charCodeAt(i);
  if (c !== BTICK && c !== TILDE) return null;
  let flen = 0;
  while (i < n && s.charCodeAt(i) === c) { flen++; i++; }
  if (flen < 3) return null;
  const infoRaw = s.slice(i);
  if (c === BTICK && infoRaw.includes('`')) return null;
  let a = 0;
  while (a < infoRaw.length && (infoRaw.charCodeAt(a) === SP || infoRaw.charCodeAt(a) === TAB)) a++;
  let infoEnd = a;
  while (infoEnd < infoRaw.length && infoRaw.charCodeAt(infoEnd) !== SP && infoRaw.charCodeAt(infoEnd) !== TAB) infoEnd++;
  let info = infoRaw.slice(a, infoEnd);
  if (info.includes('\\')) {
    let u = '';
    for (let q = 0; q < info.length; q++) {
      if (info.charCodeAt(q) === BSLASH && q + 1 < info.length && isPunct(info.charCodeAt(q + 1))) { u += info[q + 1]; q++; }
      else u += info[q];
    }
    info = u;
  }
  return { fence: c, flen, info };
}
// Setext underline: ^ {0,3}(=+|-+) *$ — returns 1 for '=', 2 for '-'.
function trySetext(s) {
  let i = 0;
  const n = s.length;
  while (i < n && (s.charCodeAt(i) === SP || s.charCodeAt(i) === TAB)) i++;
  if (i > 3) return 0;
  const c = s.charCodeAt(i);
  if (c !== EQ && c !== MINUS) return 0;
  while (i < n && s.charCodeAt(i) === c) i++;
  while (i < n && (s.charCodeAt(i) === SP || s.charCodeAt(i) === TAB)) i++;
  if (i !== n) return 0;
  return c === EQ ? 1 : 2;
}
// List marker at the cursor (indent already measured, 0..3). Returns
// {bullet, ordered, start, markerWidth, empty, pad, contentCol} or null.
// `markerOff` is the indent (column offset of the marker).
function tryListMarker(L, ind) {
  const s = L.s;
  let i = L.pos;
  // advance past the indent (ind columns) to the marker
  const savePos = L.pos, saveCol = L.col, savePtab = L.ptab;
  advance(L, ind);
  const startPos = L.pos;
  const c = peek(L);
  let bullet = false, ordered = false, start = 0, mwidth = 0;
  if (c === MINUS || c === PLUS || c === STAR) {
    bullet = true;
    mwidth = 1;
    advance(L, 1);
  } else if (isDigit(c)) {
    let j = L.pos;
    let digits = 0;
    let val = 0;
    while (j < L.len && isDigit(s.charCodeAt(j)) && digits < 10) {
      val = val * 10 + (s.charCodeAt(j) - 48);
      digits++;
      j++;
    }
    if (digits === 0 || digits > 9) { L.pos = savePos; L.col = saveCol; L.ptab = savePtab; return null; }
    const d = s.charCodeAt(j);
    if (d !== DOT && d !== RPAREN) { L.pos = savePos; L.col = saveCol; L.ptab = savePtab; return null; }
    ordered = true;
    start = val;
    mwidth = digits + 1;
    advance(L, digits + 1);
  } else {
    L.pos = savePos; L.col = saveCol; L.ptab = savePtab;
    return null;
  }
  // after the marker: spaces/tabs then content (or EOL = empty item)
  const after = measureIndent(L);
  const spaces = after.indent;
  const empty = after.blank;
  let pad;
  if (empty) {
    pad = mwidth + 1;
  } else if (spaces === 0) {
    // no space after the marker: not a list item (unless it is empty)
    L.pos = savePos; L.col = saveCol; L.ptab = savePtab;
    return null;
  } else if (spaces >= 5) {
    pad = mwidth + 1;
  } else {
    pad = mwidth + spaces;
  }
  // advance L to the item's content start (ind + pad columns from the
  // container content start); L is currently just past the marker.
  advance(L, pad - mwidth);
  return {
    bullet, ordered, start, mwidth, empty, pad,
    markerOff: ind,
    contentCol: ind + pad,
    markerChar: bullet ? String.fromCharCode(c) : (s.charCodeAt(startPos + mwidth - 1) === DOT ? '.' : ')'),
  };
}

// Split a table row/header/delimiter line into cells. Splits on '|'
// except when escaped (\|); a leading '|' drops the first cell and a
// trailing unescaped '|' drops the last. Returns array of raw cell strings.
function splitTableRow(line) {
  const cells = [];
  let cur = '';
  let i = 0;
  const n = line.length;
  while (i < n) {
    const c = line.charCodeAt(i);
    if (c === BSLASH && i + 1 < n && line.charCodeAt(i + 1) === PIPE) {
      cur += line[i + 1]; // an escaped pipe is a literal pipe in the cell
      i += 2;
    } else if (c === PIPE) {
      cells.push(cur);
      cur = '';
      i++;
    } else {
      cur += line[i];
      i++;
    }
  }
  cells.push(cur);
  if (line.charCodeAt(0) === PIPE) cells.shift();
  if (n > 0 && line.charCodeAt(n - 1) === PIPE && !(n >= 2 && line.charCodeAt(n - 2) === BSLASH)) cells.pop();
  return cells;
}
function trimCell(s) {
  let a = 0, b = s.length;
  while (a < b && (s.charCodeAt(a) === SP || s.charCodeAt(a) === TAB)) a++;
  while (b > a && (s.charCodeAt(b - 1) === SP || s.charCodeAt(b - 1) === TAB)) b--;
  return s.slice(a, b);
}
// Parse a table delimiter row. Returns array of alignments ('left' |
// 'right' | 'center' | null) or null if the line is not a delimiter row.
function parseDelimRow(line) {
  const raw = splitTableRow(line);
  if (raw.length === 0) return null;
  const aligns = [];
  for (const cell of raw) {
    const t = trimCell(cell);
    if (t.length === 0) return null;
    let left = false, right = false;
    let s = t;
    if (s.charCodeAt(0) === COLON) { left = true; s = s.slice(1); }
    if (s.length && s.charCodeAt(s.length - 1) === COLON) { right = true; s = s.slice(0, -1); }
    if (s.length === 0) return null;
    for (let k = 0; k < s.length; k++) if (s.charCodeAt(k) !== MINUS) return null;
    aligns.push(left && right ? 'center' : left ? 'left' : right ? 'right' : null);
  }
  return aligns;
}

// ---- main block parser ----
function parseBlocks(src) {
  const lines = src.split('\n');
  // a trailing newline does not create an extra blank line
  if (src.length > 0 && src.charCodeAt(src.length - 1) === NL) lines.pop();
  const root = newNode('doc');
  const defs = new Map();
  const L = makeLine();
  let lastLineBlank = false;
  let lastLineBlankTop = false;

  function saveL() { return { pos: L.pos, col: L.col, ptab: L.ptab, indent: L.indent, blank: L.blank }; }
  function restoreL(sv) { L.pos = sv.pos; L.col = sv.col; L.ptab = sv.ptab; L.indent = sv.indent; L.blank = sv.blank; }
  function commitIndent(m) { L.pos = m.pos; L.col = m.col; L.ptab = m.ptab; L.indent = m.indent; L.blank = m.blank; }

  for (let li = 0; li < lines.length; li++) {
    lineReset(L, lines[li]);
    // ---- Phase 1: match open containers ----
    let container = root;
    let allMatched = true;
    while (true) {
      const kids = container.children;
      const last = kids.length ? kids[kids.length - 1] : null;
      if (!last || !last.open) break;
      if (last.t === 'bq') {
        const m = measureIndent(L);
        if (m.indent <= 3 && m.pos < L.len && L.s.charCodeAt(m.pos) === GT) {
          commitIndent(m);
          advance(L, 1);
          const pc = peek(L);
          if (pc === SP || pc === TAB) advance(L, 1);
          container = last;
          continue;
        }
        allMatched = false;
        break;
      }
      if (last.t === 'item') {
        const m = measureIndent(L);
        if (m.blank) { container = last; continue; }
        if (m.indent >= last.markerOff + last.pad) {
          advance(L, last.markerOff + last.pad);
          container = last;
          continue;
        }
        allMatched = false;
        break;
      }
      if (last.t === 'list') { container = last; continue; }
      break;
    }
    const baseState = saveL();
    const m = measureIndent(L);
    // A line is blank when the remainder after the containers is empty,
    // or when the original line holds only whitespace. A whitespace-only
    // remainder after a container marker (e.g. ">  " leaving " ") is
    // NOT blank when a paragraph is already open: it continues that
    // paragraph (cm-241). With no paragraph open it starts none (cm-240).
    let origBlank = true;
    {
      const ol = lines[li];
      for (let q = 0; q < ol.length; q++) {
        const ch = ol.charCodeAt(q);
        if (ch !== SP && ch !== TAB) { origBlank = false; break; }
      }
    }
    const isBlank = m.blank && (L.len - baseState.pos === 0 || origBlank || tipOf(root).t !== 'p');

    // ---- blank line ----
    if (isBlank) {
      const tip0 = tipOf(root);
      if (tip0.t === 'html' && (tip0.htmlType === 6 || tip0.htmlType === 7)) tip0.endedAtBlank = true;
      // A type 1-5 HTML block loses its trailing newline only when the
      // following blank line is truly empty (not whitespace-only).
      if (lines[li].length === 0) stripHtmlTrailingNl(root);
      if (!allMatched) closeTo(root, container, defs);
      const tip = tipOf(root);
      if (tip.t === 'p') finalize(tip, defs);
      else if (tip.t === 'table') finalize(tip, defs);
      else if (tip.t === 'html' && (tip.htmlType === 6 || tip.htmlType === 7)) finalize(tip, defs);
      else if (tip.t === 'item' && tip.children.length === 0) {
        // an empty list item followed by a blank line ends the item
        // (and the list for what follows) — cm-280
        finalize(tip, defs);
      }
      else if (tip.t === 'code') {
        const strip = Math.min(tip.fenceIndent || 0, m.indent);
        if (strip > 0) advance(L, strip);
        tip.lines.push(lineContent(L));
      }
      else if (tip.t === 'icode') {
        if (m.indent >= 4) { advance(L, 4); tip.lines.push(lineContent(L)); }
        else tip.lines.push('');
      }
      else if (tip.t === 'html') tip.lines.push(lineContent(L));
      // A blank line inside a blockquote still separates blocks within
      // an enclosing list item (cm-259), but it does not separate two
      // list items from each other (cm-320): track both.
      let bt = tipOf(root);
      let inBq = false;
      while (bt) { if (bt.t === 'bq') { inBq = true; break; } bt = bt.parent; }
      lastLineBlank = true;
      lastLineBlankTop = !inBq;
      continue;
    }
    // ---- lazy continuation: the line does not match all open containers,
    // but the tip is a paragraph and the line does not start a block that
    // can interrupt a paragraph: add it to the paragraph as-is.
    if (!allMatched) {
      const tip = tipOf(root);
      if (tip.t === 'code' && tip.lines.length > 0) {
        // A fenced code block inside a LIST ITEM keeps its content lines
        // even when they do not match the item's indent — but only when
        // the container that failed to match is the list item itself. A
        // blockquote that fails to match ends the code block (cm-237).
        // A closing fence on a non-matching line does NOT close this
        // block: it falls through, closes the containers, and starts a
        // new fenced block at the outer level.
        let n = tip;
        while (n.parent && n.parent !== container) n = n.parent;
        if (n.t === 'item' && !isClosingFence(lines[li], tip.fence, tip.flen)) {
          const rawLine = lines[li];
          let ind = 0;
          while (ind < rawLine.length && (rawLine.charCodeAt(ind) === SP || rawLine.charCodeAt(ind) === TAB)) {
            if (rawLine.charCodeAt(ind) === TAB) ind += 4 - (ind % 4);
            else ind++;
          }
          const strip = Math.min(tip.fenceIndent || 0, ind);
          let cut = 0; let cols = 0;
          while (cut < rawLine.length && cols < strip) {
            if (rawLine.charCodeAt(cut) === TAB) { cols += 4 - (cols % 4); cut++; }
            else { cols++; cut++; }
          }
          tip.lines.push(rawLine.slice(cut));
          lastLineBlank = lastLineBlankTop = false;
          continue;
        }
      }
      if (tip.t === 'p' && !wouldInterruptParagraph(L, m, tip)) {
        // a lazy line indented by 4+ columns loses 4 columns of indentation
        if (m.indent >= 4) advance(L, 4);
        let content = lineContent(L);
        if (tip.lastWasLazy && trySetext(content) !== 0) content = '    ' + content;
        tip.lines.push(content);
        tip.lastWasLazy = true;
        lastLineBlank = lastLineBlankTop = false;
        continue;
      }
      closeTo(root, container, defs);
    }
    const indent = m.indent;
    let tip = tipOf(root);
    const raw = lineContent(L); // line from the container content start

    // ---- fenced code continuation ----
    if (tip.t === 'code') {
      if (isClosingFence(raw, tip.fence, tip.flen)) finalize(tip, defs);
      else {
        const strip = Math.min(tip.fenceIndent || 0, m.indent);
        if (strip > 0) { advance(L, strip); tip.lines.push(expandCodeTab(lineContent(L), L)); }
        else if (raw.charCodeAt(0) === TAB && L.col > 0) {
          // A leading tab in code content expands to spaces to the next
          // tab stop when a container indent was consumed (L.col > 0);
          // at column 0 (no container) the tab is kept literally.
          tip.lines.push(' '.repeat(4 - (L.col % 4)) + raw.slice(1));
        }
        else tip.lines.push(raw);
      }
      lastLineBlank = lastLineBlankTop = false;
      continue;
    }
    // ---- indented code continuation ----
    if (tip.t === 'icode') {
      if (indent >= 4) {
        advance(L, 4);
        tip.lines.push(expandCodeTab(lineContent(L), L));
        lastLineBlank = lastLineBlankTop = false;
        continue;
      }
      finalize(tip, defs);
      tip = tipOf(root);
    }
    // ---- table continuation ----
    if (tip.t === 'table') {
      if (indent < 4 && !startsBlock(L, m, tip)) {
        commitIndent(m);
        tip.rows.push(splitTableRow(lineContent(L)));
        lastLineBlank = lastLineBlankTop = false;
        continue;
      }
      finalize(tip, defs);
      tip = tipOf(root);
    }
    // ---- HTML block continuation (types 1-5 end on their end marker) ----
    if (tip.t === 'html') {
      tip.lines.push(raw);
      if (tip.htmlType <= 5 && htmlBlockEnds(tip, raw)) finalize(tip, defs);
      lastLineBlank = lastLineBlankTop = false;
      continue;
    }

    // ---- paragraph: setext / table / interrupt checks ----
    if (tip.t === 'p') {
      const st = trySetext(raw);
      if (st) {
        // definitions at the start of the paragraph are extracted first;
        // the heading is built from what remains (cm-215). If nothing
        // remains, this is not a heading at all (cm-216).
        const res = extractDefs(tip.lines.join('\n'), defs);
        if (res.text.trim() === '') {
          tip.lines.push(raw);
          tip.lastWasLazy = false;
          lastLineBlank = lastLineBlankTop = false;
          continue;
        }
        const parent = tip.parent;
        const idx = parent.children.indexOf(tip);
        parent.children.splice(idx, 1);
        const h = newNode('h');
        h.level = st;
        h.src = trimWs(res.text);
        h.open = false;
        addChild(parent, h);
        lastLineBlank = lastLineBlankTop = false;
        continue;
      }
      if (indent <= 3) {
        commitIndent(m);
        const delim = parseDelimRow(lineContent(L));
        if (delim) {
          const headerLine = tip.lines[tip.lines.length - 1];
          const headerCells = splitTableRow(stripLeadingWs(headerLine));
          if (headerCells.length === delim.length && headerCells.length > 0) {
            const parent = tip.parent;
            const idx = parent.children.indexOf(tip);
            tip.lines.pop();
            if (tip.lines.length === 0) parent.children.splice(idx, 1);
            else finalize(tip, defs);
            const table = newNode('table');
            table.align = delim;
            table.head = headerCells.map(trimCell);
            table.rows = [];
            addChild(parent, table);
            lastLineBlank = lastLineBlankTop = false;
            continue;
          }
        }
        restoreL(baseState);
      }
      // fall through to leaf-start attempts that can interrupt a paragraph
      if (tryLeafStart(root, L, m, tip, true, defs, lastLineBlank, lastLineBlankTop)) { lastLineBlank = lastLineBlankTop = false; continue; }
      // otherwise: add the line to the paragraph
      tip.lines.push(raw);
      tip.lastWasLazy = false;
      lastLineBlank = lastLineBlankTop = false;
      continue;
    }

    // ---- tip is a container: try leaf starts ----
    if (tryLeafStart(root, L, m, tip, false, defs, lastLineBlank, lastLineBlankTop)) { lastLineBlank = lastLineBlankTop = false; continue; }
    // no leaf start: start a paragraph (leading spaces are kept)
    closeTipList(root, defs);
    const p = newNode('p');
    p.lines = [lineContent(L)];
    p.lastWasLazy = false;
    addBlock(tipOf(root), p, lastLineBlank);
    lastLineBlank = lastLineBlankTop = false;
  }
  closeTo(root, root, defs);
  return { root, defs };
}
function stripLeadingWs(s) {
  let i = 0;
  while (i < s.length && (s.charCodeAt(i) === SP || s.charCodeAt(i) === TAB)) i++;
  return s.slice(i);
}
function trimWs(s) {
  let a = 0;
  let b = s.length;
  while (a < b && (s.charCodeAt(a) === SP || s.charCodeAt(a) === TAB || s.charCodeAt(a) === NL)) a++;
  while (b > a && (s.charCodeAt(b - 1) === SP || s.charCodeAt(b - 1) === TAB || s.charCodeAt(b - 1) === NL)) b--;
  return s.slice(a, b);
}
function isClosingFence(raw, fence, flen) {
  let i = 0;
  const n = raw.length;
  while (i < n && raw.charCodeAt(i) === SP) i++;
  if (i > 3) return false;
  let len = 0;
  while (i < n && raw.charCodeAt(i) === fence) { len++; i++; }
  if (len < flen) return false;
  while (i < n && (raw.charCodeAt(i) === SP || raw.charCodeAt(i) === TAB)) i++;
  return i === n;
}
// Does the line (at the current container content start) start a block
// that can interrupt a paragraph? Used for lazy continuations.
function wouldInterruptParagraph(L, m, tip) {
  const raw = lineContent(L);
  if (m.indent > 3) return false;
  if (m.pos < L.len && L.s.charCodeAt(m.pos) === GT) return true;
  if (isHrLine(raw)) return true;
  if (tryAtx(raw)) return true;
  if (tryFence(raw)) return true;
  if (htmlBlockStart(raw, 0, true)) return true;
  const sv = { pos: L.pos, col: L.col, ptab: L.ptab, indent: L.indent, blank: L.blank };
  const lm = tryListMarker(L, m.indent);
  L.pos = sv.pos; L.col = sv.col; L.ptab = sv.ptab; L.indent = sv.indent; L.blank = sv.blank;
  if (lm) {
    // A bullet list interrupts a paragraph whether the item is empty
    // or not. An ordered list interrupts when it starts with 1. And
    // any list marker interrupts a paragraph that is already inside a
    // list item (it ends the current item, continuing the list or
    // starting a new one).
    if (lm.bullet) return true;
    if (lm.start === 1) return true;
    if (tip) {
      let n = tip;
      while (n) {
        if (n.t === 'list') return true;
        n = n.parent;
      }
    }
  }
  return false;
}
// Does the line (at the current container content start) start a block that
// would end a table? Used for table continuation: a table row must not be
// a line that starts another block.
function startsBlock(L, m, tip) {
  const raw = lineContent(L);
  if (m.indent <= 3) {
    if (m.pos < L.len && L.s.charCodeAt(m.pos) === GT) return true;
    if (isHrLine(raw)) return true;
    if (tryAtx(raw)) return true;
    if (tryFence(raw)) return true;
    if (htmlBlockStart(raw, 0, false)) return true;
    // a list marker ends a table
    const sv = { pos: L.pos, col: L.col, ptab: L.ptab };
    const lm = tryListMarker(L, m.indent);
    L.pos = sv.pos; L.col = sv.col; L.ptab = sv.ptab;
    if (lm) return true;
  }
  return false;
}

// Add a leaf block as a child of `parent`. If the parent is a list item
// that already has a child and the previous line was blank, the list
// containing the item becomes loose.
function addBlock(parent, node, lastLineBlank) {
  if (parent.t === 'item' && parent.children.length > 0 && lastLineBlank) {
    const list = parent.parent;
    if (list && list.t === 'list') list.tight = false;
  }
  addChild(parent, node);
}
// If the deepest open block is a list, close it: a leaf block that is not
// a list item cannot be a child of a list.
function closeTipList(root, defs) {
  const tip = tipOf(root);
  if (tip.t === 'list') finalize(tip, defs);
}
// Try to start a leaf block at the current line (L at the container
// content start, m = measureIndent result). `tip` is the deepest open
// block (a container, or a paragraph when inParagraph). Returns true if
// the line was consumed by a new leaf block. When a list item is started,
// the rest of the line is processed as the item's content (recursively).
function tryLeafStart(root, L, m, tip, inParagraph, defs, lastLineBlank, lastLineBlankTop) {
  const raw = lineContent(L);
  const indent = m.indent;
  const base = { pos: L.pos, col: L.col, ptab: L.ptab, indent: L.indent, blank: L.blank };
  function restore() { L.pos = base.pos; L.col = base.col; L.ptab = base.ptab; L.indent = base.indent; L.blank = base.blank; }

  if (indent <= 3) {
    // Blockquote: open a new blockquote container.
    if (m.pos < L.len && L.s.charCodeAt(m.pos) === GT) {
      if (inParagraph) finalize(tip, defs);
      closeTipList(root, defs);
      const bq = newNode('bq');
      addBlock(tipOf(root), bq, lastLineBlank);
      L.pos = m.pos; L.col = m.col; L.ptab = m.ptab;
      advance(L, 1);
      const pc2 = peek(L);
      if (pc2 === SP || pc2 === TAB) advance(L, 1);
      const m2 = measureIndent(L);
      if (m2.blank) return true;
      const started = tryLeafStart(root, L, m2, bq, false, defs, lastLineBlank, lastLineBlankTop);
      if (!started) {
        const p = newNode('p');
        p.lines = [lineContent(L)];
        p.lastWasLazy = false;
        addBlock(bq, p, lastLineBlank);
      }
      return true;
    }
    if (isHrLine(raw)) {
      if (inParagraph) finalize(tip, defs);
      closeTipList(root, defs);
      const hr = newNode('hr'); hr.open = false;
      addBlock(tipOf(root), hr, lastLineBlank);
      return true;
    }
    const atx = tryAtx(raw);
    if (atx) {
      if (inParagraph) finalize(tip, defs);
      closeTipList(root, defs);
      const h = newNode('h'); h.level = atx.level; h.src = atx.src; h.open = false;
      addBlock(tipOf(root), h, lastLineBlank);
      return true;
    }
    const fence = tryFence(raw);
    if (fence) {
      if (inParagraph) finalize(tip, defs);
      closeTipList(root, defs);
      const code = newNode('code');
      code.fence = fence.fence; code.flen = fence.flen; code.info = fence.info;
      code.fenceIndent = indent; code.lines = [];
      addBlock(tipOf(root), code, lastLineBlank);
      return true;
    }
    const hb = htmlBlockStart(raw, 0, inParagraph);
    if (hb) {
      if (inParagraph) finalize(tip, defs);
      closeTipList(root, defs);
      const html = newNode('html');
      html.htmlType = hb.type; html.htmlEnd = hb.end; html.lines = [raw];
      addBlock(tipOf(root), html, lastLineBlank);
      if (hb.type <= 5 && htmlBlockEnds(html, raw)) finalize(html, defs);
      return true;
    }
    const lm = tryListMarker(L, indent);
    if (lm) {
      if (inParagraph) {
        // A bullet list interrupts a paragraph whether the item is empty
        // or not; an ordered list interrupts when it starts with 1, or
        // (any start) when the paragraph is already inside a list item.
        let canInterrupt = false;
        if (!lm.empty) {
          if (lm.bullet || lm.start === 1) canInterrupt = true;
          else {
            let n = tip;
            while (n) { if (n.t === 'list') { canInterrupt = true; break; } n = n.parent; }
          }
        }
        if (!canInterrupt) { restore(); return false; }
        finalize(tip, defs);
      }
      let container = tipOf(root);
      const kind = lm.bullet ? 'bullet' : 'ordered';
      let list = null;
      if (container.t === 'list' && container.kind === kind && container.marker === lm.markerChar) {
        // the tip is a list of the matching type: add an item to it
        list = container;
        if (lastLineBlankTop) list.tight = false;
      } else {
        if (container.t === 'list') {
          // a list of a different type: close it; the new list is a sibling
          finalize(container, defs);
          container = container.parent;
        }
        const kids = container.children;
        const lastChild = kids.length ? kids[kids.length - 1] : null;
        if (lastChild && lastChild.t === 'list' && lastChild.open &&
            lastChild.kind === kind && lastChild.marker === lm.markerChar) {
          list = lastChild;
          if (lastLineBlankTop) list.tight = false;
        } else {
          list = newNode('list');
          list.kind = kind;
          list.marker = lm.markerChar;
          list.start = lm.start;
          list.tight = true;
          addBlock(container, list, lastLineBlank);
        }
      }
      const item = newNode('item');
      item.markerOff = lm.markerOff;
      item.pad = lm.pad;
      addChild(list, item);
      // process the rest of the line as the item's content
      if (!lm.empty) {
        const m2 = measureIndent(L);
        if (!m2.blank) {
          const started = tryLeafStart(root, L, m2, item, false, defs, lastLineBlank, lastLineBlankTop);
          if (!started) {
            const p = newNode('p');
            p.lines = [lineContent(L)];
            p.lastWasLazy = false;
            addBlock(item, p, lastLineBlank);
          }
        }
      }
      return true;
    }
  }
  if (!inParagraph && indent >= 4) {
    closeTipList(root, defs);
    const code = newNode('icode');
    advance(L, 4);
    code.lines = [lineContent(L)];
    addBlock(tipOf(root), code, lastLineBlank);
    return true;
  }
  return false;
}

// ---- inline parser ----
// Inline node types: text, code, em, strong, del, link, img, html, br,
// delim (temporary emphasis/strikethrough delimiter), opener (temporary
// link/image bracket). Nodes form a doubly-linked list via next/prev.
function newInNode(t) {
  return { t, s: '', href: '', title: '', children: null, next: null, prev: null,
    ch: 0, len: 0, canOpen: false, canClose: false, isImage: false, active: true };
}
function inAppend(list, node) {
  if (list.tail) { list.tail.next = node; node.prev = list.tail; list.tail = node; }
  else { list.head = node; list.tail = node; }
}
// left/right flanking for a delimiter run src[i..j) (j exclusive).
function flank(src, i, j) {
  const before = i > 0 ? src.charCodeAt(i - 1) : -1;
  const after = j < src.length ? src.charCodeAt(j) : -1;
  const beforeWs = before < 0 || isUniWs(before);
  const afterWs = after < 0 || isUniWs(after);
  const beforePunct = before >= 0 && isUniPunct(before);
  const afterPunct = after >= 0 && isUniPunct(after);
  const left = !afterWs && (!afterPunct || beforeWs || beforePunct);
  const right = !beforeWs && (!beforePunct || afterWs || afterPunct);
  return { left, right, before, after };
}
// Decode a numeric entity starting at src[i] ('&'). Returns {len, cp}
// where len is the full entity length and cp the code point, or null.
function numericEntity(src, i) {
  if (src.charCodeAt(i) !== AMP || src.charCodeAt(i + 1) !== HASH) return null;
  let j = i + 2;
  let hex = false;
  if (src.charCodeAt(j) === 120 || src.charCodeAt(j) === 88) { hex = true; j++; }
  const d0 = j;
  let v = 0;
  let digits = 0;
  if (hex) {
    while (j < src.length) {
      const c = src.charCodeAt(j);
      let d = -1;
      if (c >= 48 && c <= 57) d = c - 48;
      else if (c >= 97 && c <= 102) d = c - 87;
      else if (c >= 65 && c <= 70) d = c - 55;
      if (d < 0) break;
      digits++;
      if (digits <= 6) v = v * 16 + d;
      j++;
    }
    if (digits === 0 || digits > 6) return null;
  } else {
    while (j < src.length && isDigit(src.charCodeAt(j))) {
      digits++;
      if (digits <= 7) v = v * 10 + (src.charCodeAt(j) - 48);
      j++;
    }
    if (digits === 0 || digits > 7) return null;
  }
  if (j >= src.length || src.charCodeAt(j) !== SEMI) return null;
  if (v === 0 || v > 0x10FFFF || (v >= 0xD800 && v <= 0xDFFF)) v = 0xFFFD;
  return { len: j - i + 1, cp: v };
}
// A valid entity-like sequence at src[i]: named (&word;) or numeric.
// Named entities are never decoded, but the '&' is left unescaped.
function entityLike(src, i) {
  if (src.charCodeAt(i) !== AMP) return 0;
  const n = numericEntity(src, i);
  if (n) return n.len;
  let j = i + 1;
  while (j < src.length && isAlnum(src.charCodeAt(j))) j++;
  if (j > i + 1 && j < src.length && src.charCodeAt(j) === SEMI) return j - i + 1;
  return 0;
}
// Parse a link label [..] starting at s[i] ('['). Returns {label, end}
// (end = index just after ']') or null.
function parseLabelAt(s, i) {
  let j = i + 1;
  let len = 0;
  while (j < s.length) {
    const c = s.charCodeAt(j);
    if (c === BACKSLASH) { j += 2; len += 2; continue; }
    if (c === LBRACK) return null; // an unescaped '[' is not allowed
    if (c === RBRACK) {
      // the label ends at the first unescaped ']' (no depth counting)
      return { label: s.slice(i + 1, j), end: j + 1 };
    }
    j++; len++;
    if (len > 999) return null;
  }
  return null;
}
// Parse an inline link (dest "title") starting at s[i] ('(').
function parseInlineLinkAt(s, i) {
  let j = skipInlineWs(s, i + 1, true);
  if (j < 0 || j >= s.length) return null;
  if (s.charCodeAt(j) === RPAREN) return { href: '', title: '', end: j + 1 };
  const d = parseDest(s, j);
  if (!d) return null;
  let title = '';
  let k = skipInlineWs(s, d.next, true);
  if (k < 0) return null;
  if (k < s.length && s.charCodeAt(k) !== RPAREN) {
    const t = parseTitle(s, k);
    if (!t) return null;
    title = t.title;
    k = skipInlineWs(s, t.next, true);
    if (k < 0) return null;
  }
  if (k >= s.length || s.charCodeAt(k) !== RPAREN) return null;
  return { href: d.dest, title, end: k + 1 };
}
// Backpedal-trim a candidate extended-autolink URL.
function backpedalUrl(s) {
  for (;;) {
    const lo = s.lastIndexOf('(');
    if (lo < 0) break;
    if (s.indexOf(')', lo) < 0) { s = s.slice(0, lo); continue; }
    break;
  }
  // Trim trailing punctuation, unmatched trailing ')' and trailing
  // entity-like sequences repeatedly: stripping one can reveal another
  // (e.g. "http://x)." -> "http://x", "www.x/?q=a&hl;" -> "www.x/?q=a").
  // The entity check runs before punctuation trimming so the ';' of an
  // entity like &hl; is not stripped first.
  for (;;) {
    let changed = false;
    const amp = s.lastIndexOf('&');
    if (amp >= 0) {
      const tail = s.slice(amp);
      if (/^&[a-zA-Z0-9]+;$/.test(tail)) { s = s.slice(0, amp); changed = true; }
      else if (/^&#[0-9]+;$/.test(tail) || /^&#[xX][0-9a-fA-F]+;$/.test(tail)) { s = s.slice(0, -1); changed = true; }
    }
    while (s.length > 0 && '?!.,:;*_~'.indexOf(s[s.length - 1]) >= 0) { s = s.slice(0, -1); changed = true; }
    if (s.endsWith(')')) {
      let depth = 0;
      let matchIdx = -1;
      for (let k = s.length - 1; k >= 0; k--) {
        const ch = s[k];
        if (ch === ')') depth++;
        else if (ch === '(') {
          depth--;
          if (depth === 0) { matchIdx = k; break; }
        }
      }
      if (matchIdx < 0 || matchIdx !== s.lastIndexOf('(')) { s = s.slice(0, -1); changed = true; }
    }
    if (!changed) break;
  }
  return s;
}
function isUrlChar(c) {
  return c > 32 && c !== LT && c !== GT;
}
// Try an extended autolink at src[i]. Returns {end, href, text} or null.
// Schemes: http/https/ftp + :// ; www. ; email ; mailto:/xmpp: + email.
// Inside a '[' label, the URL stops at ']' (the label closer) and '['.
function tryExtendedAutolink(src, i, inLabel) {
  const n = src.length;
  const urlChar = (c) => c > 32 && c !== LT && c !== GT && !(inLabel && (c === 91 || c === 93));
  const prev = i > 0 ? src.charCodeAt(i - 1) : -1;
  const prevIsAlnum = prev >= 0 && isAlnum(prev);
  const prevIsSchemeChar = prevIsAlnum || prev === 43 || prev === 45 || prev === 46;
  // www.
  if (!prevIsAlnum && src.startsWith('www.', i)) {
    let j = i + 4;
    if (j >= n || src.charCodeAt(j) === DOT) return null;
    let k = j;
    while (k < n) {
      const c = src.charCodeAt(k);
      if (isAlnum(c) || c === UNDERSCORE || c === MINUS || c === DOT) k++;
      else break;
    }
    if (k === j) return null;
    let dom = src.slice(j, k);
    while (dom.endsWith('_') || dom.endsWith('.')) dom = dom.slice(0, -1);
    if (dom.length === 0) return null;
    // the path/query after the domain is part of the link too
    let e = i + 4 + dom.length;
    while (e < n && urlChar(src.charCodeAt(e))) e++;
    let text = backpedalUrl(src.slice(i, e));
    if (text.length <= 4) return null;
    return { end: i + text.length, href: 'http://' + text, text };
  }
  // scheme:// (http, https, ftp)
  if (!prevIsSchemeChar) {
    let j = i;
    if (j < n && isAlpha(src.charCodeAt(j))) {
      let k = j + 1;
      while (k < n) {
        const c = src.charCodeAt(k);
        if (isAlnum(c) || c === 43 || c === 45 || c === 46) k++;
        else break;
      }
      const scheme = src.slice(j, k);
      const slow = scheme.toLowerCase();
      if ((slow === 'http' || slow === 'https' || slow === 'ftp') &&
          src.startsWith('://', k)) {
        let e = k + 3;
        while (e < n && urlChar(src.charCodeAt(e))) e++;
        let u = backpedalUrl(src.slice(i, e));
        if (u.length > scheme.length + 3) {
          return { end: i + u.length, href: u, text: u };
        }
      }
      // mailto: / xmpp: + email
      if ((slow === 'mailto' || slow === 'xmpp') && k < n && src.charCodeAt(k) === COLON) {
        const em = scanEmail(src, k + 1);
        if (em) {
          let end = em.end;
          let text = src.slice(i, end);
          if (slow === 'xmpp' && end < n && src.charCodeAt(end) === SLASH) {
            const res = scanXmppResource(src, end);
            if (res) { end = res.end; text = src.slice(i, end); }
          }
          return { end, href: text, text };
        }
      }
    }
  }
  // bare email (local@domain)
  if (!prevIsAlnum && prev !== 46 && prev !== 43 && prev !== 45 && prev !== UNDERSCORE) {
    let j = i;
    while (j < n) {
      const c = src.charCodeAt(j);
      if (isAlnum(c) || c === DOT || c === 43 || c === MINUS || c === UNDERSCORE) j++;
      else break;
    }
    if (j > i && j < n && src.charCodeAt(j) === AT) {
      const em = scanEmail(src, i);
      if (em) return { end: em.end, href: 'mailto:' + em.text, text: em.text };
    }
  }
  return null;
}
// Scan an email starting at src[i]. Returns {end, text} or null.
function scanEmail(src, i) {
  const n = src.length;
  let j = i;
  while (j < n) {
    const c = src.charCodeAt(j);
    if (isAlnum(c) || c === DOT || c === 43 || c === MINUS || c === UNDERSCORE) j++;
    else break;
  }
  if (j === i || j >= n || src.charCodeAt(j) !== AT) return null;
  const local = src.slice(i, j);
  if (local.length === 0) return null;
  let k = j + 1;
  let d0 = k;
  while (k < n) {
    const c = src.charCodeAt(k);
    if (isAlnum(c) || c === UNDERSCORE || c === MINUS || c === DOT) k++;
    else break;
  }
  if (k === d0) return null;
  let dom = src.slice(d0, k);
  while (dom.endsWith('.')) dom = dom.slice(0, -1);
  if (dom.length === 0) return null;
  if (dom.endsWith('-') || dom.endsWith('_')) return null;
  const labels = dom.split('.');
  if (labels.length < 2) return null;
  for (const lab of labels) {
    if (lab.length === 0) return null;
  }
  const lastLab = labels[labels.length - 1];
  if (!isAlnum(lastLab.charCodeAt(lastLab.length - 1))) return null;
  const text = local + '@' + dom;
  return { end: i + text.length, text };
}
// Scan an xmpp resource /name[@host[.host]*] starting at src[i] ('/').
function scanXmppResource(src, i) {
  const n = src.length;
  let j = i + 1;
  let k = j;
  while (k < n && isAlnum(src.charCodeAt(k))) k++;
  if (k === j) return null;
  let end = k;
  if (k < n && src.charCodeAt(k) === AT) {
    let m = k + 1;
    let h0 = m;
    while (m < n && isAlnum(src.charCodeAt(m))) m++;
    if (m === h0) return null;
    end = m;
    while (end + 1 < n && src.charCodeAt(end) === DOT && isAlnum(src.charCodeAt(end + 1))) {
      let p = end + 1;
      while (p < n && isAlnum(src.charCodeAt(p))) p++;
      end = p;
    }
  }
  return { end };
}
// Try an autolink <...> or inline raw HTML at src[i] ('<').
// Returns {end, kind, href, html} or null.
function tryAngle(src, i) {
  const n = src.length;
  // autolink <scheme:...> or <email>
  let j = i + 1;
  if (j < n) {
    const c = src.charCodeAt(j);
    if (isAlpha(c)) {
      // scheme
      let k = j + 1;
      while (k < n) {
        const ch = src.charCodeAt(k);
        if (isAlnum(ch) || ch === 43 || ch === 45 || ch === 46) k++;
        else break;
      }
      if (k < n && src.charCodeAt(k) === COLON && k - j >= 2 && k - j <= 32) {
        let e = k + 1;
        while (e < n && src.charCodeAt(e) !== GT && src.charCodeAt(e) !== SP &&
               src.charCodeAt(e) !== TAB && src.charCodeAt(e) !== LF && src.charCodeAt(e) !== LT) e++;
        if (e < n && src.charCodeAt(e) === GT && e > k + 1) {
          const text = src.slice(i + 1, e);
          return { end: e + 1, kind: 'link', href: text, html: text };
        }
      }
      // email
      const em = scanEmail(src, j);
      if (em && em.end < n && src.charCodeAt(em.end) === GT) {
        return { end: em.end + 1, kind: 'link', href: 'mailto:' + em.text, html: em.text };
      }
    }
  }
  // raw HTML inline
  const htmlEnd = scanInlineHtml(src, i);
  if (htmlEnd > 0) return { end: htmlEnd, kind: 'html', href: '', html: src.slice(i, htmlEnd) };
  return null;
}
// Scan inline raw HTML starting at src[i] ('<'). Returns end index or -1.
function scanInlineHtml(src, i) {
  const n = src.length;
  if (src.startsWith('<!--', i)) {
    // "<!-->" is an empty comment; "<!--->" holds a single '-'
    if (src.charCodeAt(i + 4) === GT) return i + 5;
    if (src.startsWith('->', i + 4)) return i + 6;
    let k = src.indexOf('-->', i + 4);
    return k < 0 ? -1 : k + 3;
  }
  if (src.startsWith('<?', i)) {
    let k = src.indexOf('?>', i + 2);
    return k < 0 ? -1 : k + 2;
  }
  if (src.startsWith('<![CDATA[', i)) {
    let k = src.indexOf(']]>', i + 9);
    return k < 0 ? -1 : k + 3;
  }
  if (src.startsWith('<!', i)) {
    let k = i + 2;
    if (k < n && isAlpha(src.charCodeAt(k))) {
      while (k < n && src.charCodeAt(k) !== GT) k++;
      return k < n ? k + 1 : -1;
    }
    return -1;
  }
  // closing tag
  if (src.startsWith('</', i)) {
    let k = i + 2;
    if (k < n && isAlpha(src.charCodeAt(k))) {
      k++;
      while (k < n && (isAlnum(src.charCodeAt(k)) || src.charCodeAt(k) === MINUS)) k++;
      while (k < n && (src.charCodeAt(k) === SP || src.charCodeAt(k) === TAB || src.charCodeAt(k) === LF)) k++;
      if (k < n && src.charCodeAt(k) === GT) return k + 1;
    }
    return -1;
  }
  // open tag
  if (i + 1 < n && isAlpha(src.charCodeAt(i + 1))) {
    let k = i + 1;
    k++;
    while (k < n && (isAlnum(src.charCodeAt(k)) || src.charCodeAt(k) === MINUS)) k++;
    // the tag name must be followed by whitespace, '>', '/' or end
    if (k < n) {
      const c0 = src.charCodeAt(k);
      if (!(c0 === SP || c0 === TAB || c0 === LF || c0 === GT || c0 === SLASH)) return -1;
    }
    let firstAttr = true;
    let hadWs = false;
    for (;;) {
      while (k < n && (src.charCodeAt(k) === SP || src.charCodeAt(k) === TAB || src.charCodeAt(k) === LF)) { k++; hadWs = true; }
      if (k >= n) return -1;
      const c = src.charCodeAt(k);
      if (c === GT) return k + 1;
      if (c === SLASH) {
        if (k + 1 < n && src.charCodeAt(k + 1) === GT) return k + 2;
        return -1;
      }
      if (!firstAttr && !hadWs) return -1; // attributes need whitespace
      firstAttr = false;
      hadWs = false;
      // attribute name
      if (!(isAlpha(c) || c === UNDERSCORE || c === COLON)) return -1;
      k++;
      while (k < n) {
        const ch = src.charCodeAt(k);
        if (isAlnum(ch) || ch === UNDERSCORE || ch === COLON || ch === DOT || ch === MINUS) k++;
        else break;
      }
      while (k < n && (src.charCodeAt(k) === SP || src.charCodeAt(k) === TAB || src.charCodeAt(k) === LF)) { k++; hadWs = true; }
      if (k < n && src.charCodeAt(k) === 61) { // '='
        k++;
        while (k < n && (src.charCodeAt(k) === SP || src.charCodeAt(k) === TAB || src.charCodeAt(k) === LF)) k++;
        if (k >= n) return -1;
        const q = src.charCodeAt(k);
        if (q === QUOT || q === SQUOT) {
          k++;
          while (k < n && src.charCodeAt(k) !== q) k++;
          if (k >= n) return -1;
          k++;
        } else {
          while (k < n) {
            const ch = src.charCodeAt(k);
            if (ch === SP || ch === TAB || ch === LF || ch === GT || ch === QUOT || ch === SQUOT || ch === 61 || ch === LT || ch === BACKTICK) break;
            k++;
          }
          if (k >= n) return -1;
        }
        hadWs = false;
      }
    }
  }
  return -1;
}

// Resolve emphasis/strikethrough within one container (a node array).
// `delims` is the global delimiter list; only delimiters whose container
// is this array participate. Mutates the array in place and returns it.
function resolveEmphasis(nodes, delims) {
  let i = 0;
  while (i < delims.length) {
    const closer = delims[i];
    if (closer.container !== nodes || closer.len === 0 || !closer.canClose) { i++; continue; }
    let opener = null;
    for (let j = i - 1; j >= 0; j--) {
      const op = delims[j];
      if (op.container !== nodes || op.len === 0 || !op.canOpen) continue;
      if (op.ch !== closer.ch) continue;
      // the "odd match" rule only applies when one of the two delimiters
      // can both open and close emphasis
      const bothCapable = (op.canOpen && op.canClose) || (closer.canOpen && closer.canClose);
      const oddMatch = bothCapable && (op.len + closer.len) % 3 === 0 && (op.len % 3 !== 0 || closer.len % 3 !== 0);
      if (oddMatch) continue;
      opener = op;
      break;
    }
    if (!opener) { i++; continue; }
    const useDelims = (opener.len >= 2 && closer.len >= 2) ? 2 : 1;
    opener.len -= useDelims;
    closer.len -= useDelims;
    const oi = nodes.indexOf(opener);
    const ci = nodes.indexOf(closer);
    if (oi < 0 || ci < 0 || ci <= oi) { if (closer.len === 0) i++; continue; }
    const children = nodes.slice(oi + 1, ci);
    const type = opener.ch === TILDE ? 'del' : (useDelims === 2 ? 'strong' : 'em');
    const em = newInNode(type);
    em.children = children;
    for (const ch of children) ch.container = children;
    const replacement = [];
    if (opener.len > 0) replacement.push(opener);
    replacement.push(em);
    if (closer.len > 0) replacement.push(closer);
    nodes.splice(oi, ci - oi + 1, ...replacement);
    if (closer.len === 0) i++;
  }
  return nodes;
}
// Plain-text rendering of inline nodes (for image alt text).
function plainText(nodes) {
  let out = '';
  for (const nd of nodes) {
    if (nd.t === 'text' || nd.t === 'code') out += nd.s;
    else if (nd.t === 'html') out += nd.s;
    else if (nd.t === 'delim') out += String.fromCharCode(nd.ch).repeat(nd.len);
    else if (nd.t === 'opener') out += nd.s;
    else if (nd.t === 'img') out += nd.alt || '';
    else if (nd.children) out += plainText(nd.children);
  }
  return out;
}
function renderInlineNodes(nodes) {
  let out = '';
  for (const nd of nodes) {
    if (nd.t === 'text') out += nd.s;
    else if (nd.t === 'code') out += '<code>' + nd.s + '</code>';
    else if (nd.t === 'em') out += '<em>' + renderInlineNodes(nd.children) + '</em>';
    else if (nd.t === 'strong') out += '<strong>' + renderInlineNodes(nd.children) + '</strong>';
    else if (nd.t === 'del') out += '<del>' + renderInlineNodes(nd.children) + '</del>';
    else if (nd.t === 'link') {
      out += '<a href="' + escapeHtml(cleanUrl(nd.href), false) + '"';
      if (nd.title) out += ' title="' + escapeHtml(nd.title, false) + '"';
      out += '>' + renderInlineNodes(nd.children) + '</a>';
    } else if (nd.t === 'img') {
      out += '<img src="' + escapeHtml(cleanUrl(nd.src), false) + '" alt="' + escapeHtml(nd.alt || '', false) + '"';
      if (nd.title) out += ' title="' + escapeHtml(nd.title, false) + '"';
      out += '>';
    } else if (nd.t === 'html') out += nd.s;
    else if (nd.t === 'br') out += '<br>';
    else if (nd.t === 'delim') out += String.fromCharCode(nd.ch).repeat(nd.len);
    else if (nd.t === 'opener') out += nd.s;
  }
  return out;
}
function parseInline(src, defs) {
  const nodes = [];
  const delims = [];
  const n = src.length;
  let i = 0;
  function textNode() {
    const last = nodes[nodes.length - 1];
    if (last && last.t === 'text') return last;
    const t = newInNode('text');
    t.container = nodes;
    nodes.push(t);
    return t;
  }
  function addCharEscaped(c) {
    const t = textNode();
    if (c === AMP) t.s += '&amp;';
    else if (c === LT) t.s += '&lt;';
    else if (c === GT) t.s += '&gt;';
    else if (c === QUOT) t.s += '&quot;';
    else if (c === SQUOT) t.s += '&#39;';
    else t.s += String.fromCharCode(c);
  }
  function addRaw(s) { textNode().s += s; }
  function lookupRef(label) {
    // Reference labels are matched raw (no backslash unescaping):
    // [foo\!] does not match a [foo!] definition (cm-545), while
    // [Foo*bar\]] matches [Foo*bar\]] (cm-194).
    const key = normalizeLabel(label);
    const d = defs.get(key);
    return d || null;
  }
  // True when the scan is inside an unmatched '[' label: an extended
  // autolink must not form there (it would nest a link inside the label).
  function inLabel() {
    for (let k = delims.length - 1; k >= 0; k--) {
      const d = delims[k];
      if (d.t === 'opener') return d.active;
    }
    return false;
  }
  function formLink(closeIdx) {
    // find the nearest active opener
    let opPos = -1;
    for (let k = delims.length - 1; k >= 0; k--) {
      const d = delims[k];
      if (d.t === 'opener' && d.active) { opPos = k; break; }
    }
    if (opPos < 0) return -1;
    const opener = delims[opPos];
    const openerIdx = nodes.indexOf(opener);
    if (openerIdx < 0) return -1;
    // raw label text between [ and ]
    const rawLabel = src.slice(opener.labelStart, closeIdx);
    // the label's brackets must balance (an unmatched '[' inside it
    // means this ']' does not close this opener)
    let bal = 0;
    for (let q = 0; q < rawLabel.length; q++) {
      const qc = rawLabel.charCodeAt(q);
      if (qc === BSLASH) { q++; continue; }
      if (qc === LB) bal++;
      else if (qc === RB) { if (--bal < 0) break; }
    }
    if (bal !== 0) return -1; // this ']' does not close this opener; the
    // opener stays active for a later ']'
    let href = null;
    let title = '';
    let end = closeIdx + 1;
    const nx = end < n ? src.charCodeAt(end) : -1;
    if (nx === LPAREN) {
      const il = parseInlineLinkAt(src, end);
      if (!il) {
        // not a valid inline link: fall back to a shortcut reference
        const ref = lookupRef(rawLabel);
        if (!ref) { opener.active = false; return -1; }
        href = ref.dest; title = ref.title;
      } else {
        href = il.href; title = il.title; end = il.end;
      }
    } else if (nx === LBRACK) {
      const lab = parseLabelAt(src, end);
      if (lab) {
        const ref = lab.label.length === 0 ? lookupRef(rawLabel) : lookupRef(lab.label);
        if (!ref) { opener.active = false; return -1; }
        href = ref.dest; title = ref.title; end = lab.end;
      } else {
        const ref = lookupRef(rawLabel);
        if (!ref) { opener.active = false; return -1; }
        href = ref.dest; title = ref.title;
      }
    } else {
      const ref = lookupRef(rawLabel);
      if (!ref) { opener.active = false; return -1; }
      href = ref.dest; title = ref.title;
    }
    // build the link/image node from the nodes after the opener
    const children = nodes.slice(openerIdx + 1);
    for (const ch of children) {
      if (ch.t === 'opener') ch.active = false;
      ch.container = children;
    }
    // A link cannot contain another link: when a link (not an image)
    // forms, deactivate every preceding *link* opener (its link text
    // would contain this link). Image openers stay active: an image may
    // contain a link in its label.
    if (!opener.isImage) {
      for (let k = 0; k < opPos; k++) {
        const d = delims[k];
        if (d.t === 'opener' && !d.isImage) d.active = false;
      }
    }
    const link = newInNode(opener.isImage ? 'img' : 'link');
    if (opener.isImage) {
      link.src = href;
      link.title = title;
      // emphasis inside the label is resolved for the alt text
      resolveEmphasis(children, delims);
      link.alt = plainText(children);
    } else {
      link.href = href;
      link.title = title;
      link.children = children;
    }
    link.container = nodes;
    nodes.length = openerIdx;
    nodes.push(link);
    opener.active = false;
    return end;
  }
  while (i < n) {
    const c = src.charCodeAt(i);
    if (c === BACKTICK) {
      let j = i;
      while (j < n && src.charCodeAt(j) === BACKTICK) j++;
      const run = j - i;
      let k = j;
      let found = -1;
      while (k < n) {
        if (src.charCodeAt(k) === BACKTICK) {
          let e = k;
          while (e < n && src.charCodeAt(e) === BACKTICK) e++;
          if (e - k === run) { found = k; break; }
          k = e;
        } else k++;
      }
      if (found < 0) {
        // no matching closer: the whole backtick run is literal text
        for (let q = i; q < j; q++) addCharEscaped(BTICK);
        i = j;
        continue;
      }
      let content = src.slice(j, found);
      content = content.replace(/\n/g, ' ');
      if (content.length >= 2 && content.charCodeAt(0) === SP &&
          content.charCodeAt(content.length - 1) === SP && content.trim().length > 0) {
        content = content.slice(1, -1);
      }
      const code = newInNode('code');
      code.s = escapeHtml(content, true);
      code.container = nodes;
      nodes.push(code);
      i = found + run;
      continue;
    }
    if (c === STAR || c === UNDERSCORE || c === TILDE) {
      let j = i;
      while (j < n && src.charCodeAt(j) === c) j++;
      const run = j - i;
      const fl = flank(src, i, j);
      const d = newInNode('delim');
      d.ch = c;
      d.len = run;
      d.container = nodes;
      if (c === UNDERSCORE) {
        d.canOpen = fl.left && (!fl.right || isUniPunct(fl.before));
        d.canClose = fl.right && (!fl.left || isUniPunct(fl.after));
      } else {
        d.canOpen = fl.left;
        d.canClose = fl.right;
      }
      if (c === TILDE && run >= 3) { d.canOpen = false; d.canClose = false; }
      nodes.push(d);
      delims.push(d);
      i = j;
      continue;
    }
    if (c === BACKSLASH) {
      const nx = i + 1 < n ? src.charCodeAt(i + 1) : -1;
      if (nx === LF) {
        const br = newInNode('br');
        br.container = nodes;
        nodes.push(br);
        i += 2;
        // after a hard break, leading spaces of the next line are dropped
        while (i < n && (src.charCodeAt(i) === SP || src.charCodeAt(i) === TAB)) i++;
        continue;
      }
      if (nx >= 0 && isPunct(nx)) { addCharEscaped(nx); i += 2; continue; }
      addCharEscaped(c); i++; continue;
    }
    if (c === AMP) {
      const ne = numericEntity(src, i);
      if (ne) {
        const cp = ne.cp;
        if (cp === 34 || cp === 38 || cp === 39 || cp === 60 || cp === 62) addCharEscaped(cp);
        else addRaw(String.fromCodePoint(cp));
        i += ne.len;
        continue;
      }
      const el = entityLike(src, i);
      if (el > 0) { addRaw(src.slice(i, i + el)); i += el; continue; }
      addCharEscaped(c); i++; continue;
    }
    if (c === LT) {
      const ang = tryAngle(src, i);
      if (ang) {
        if (ang.kind === 'link') {
          const link = newInNode('link');
          link.href = ang.href;
          const t = newInNode('text');
          t.s = escapeHtml(ang.html, true);
          t.container = [t];
          link.children = [t];
          link.container = nodes;
          nodes.push(link);
        } else {
          const h = newInNode('html');
          h.s = ang.html;
          h.container = nodes;
          nodes.push(h);
        }
        i = ang.end;
        continue;
      }
      addCharEscaped(c); i++; continue;
    }
    if (c === BANG && i + 1 < n && src.charCodeAt(i + 1) === LBRACK) {
      const op = newInNode('opener');
      op.s = '![';
      op.isImage = true;
      op.labelStart = i + 2;
      op.container = nodes;
      nodes.push(op);
      delims.push(op);
      i += 2;
      continue;
    }
    if (c === LBRACK) {
      const op = newInNode('opener');
      op.s = '[';
      op.isImage = false;
      op.labelStart = i + 1;
      op.container = nodes;
      nodes.push(op);
      delims.push(op);
      i++;
      continue;
    }
    if (c === RBRACK) {
      const end = formLink(i);
      if (end > 0) { i = end; continue; }
      addCharEscaped(c); i++; continue;
    }
    if (c === LF) {
      let k = i - 1;
      let spaces = 0;
      while (k >= 0 && src.charCodeAt(k) === SP) { spaces++; k--; }
      if (spaces >= 2) {
        const last = nodes[nodes.length - 1];
        if (last && last.t === 'text') last.s = last.s.replace(/ +$/, '');
        const br = newInNode('br');
        br.container = nodes;
        nodes.push(br);
        i++;
        // after a hard break, leading spaces of the next line are dropped
        while (i < n && (src.charCodeAt(i) === SP || src.charCodeAt(i) === TAB)) i++;
      } else {
        const t = newInNode('text');
        t.s = '\n';
        t.container = nodes;
        nodes.push(t);
        i++;
      }
      continue;
    }
    // extended autolink (www. / email / scheme); never inside a '[' label
    if (isAlnum(c) && !inLabel()) {
      const ea = tryExtendedAutolink(src, i, inLabel());
      if (ea) {
        const link = newInNode('link');
        link.href = ea.href;
        const t = newInNode('text');
        t.s = escapeHtml(ea.text, true);
        t.container = [t];
        link.children = [t];
        link.container = nodes;
        nodes.push(link);
        i = ea.end;
        continue;
      }
    }
    addCharEscaped(c);
    i++;
  }
  // resolve emphasis per container (top level + each link's children).
  // resolveEmphasis mutates each container array in place.
  resolveEmphasis(nodes, delims);
  const containers = [];
  (function collect(ns) {
    for (const nd of ns) {
      if (nd.children) {
        if (nd.t === 'link') containers.push(nd.children);
        collect(nd.children);
      }
    }
  })(nodes);
  for (const cont of containers) resolveEmphasis(cont, delims);
  return renderInlineNodes(nodes);
}

// ---- block renderer ----
function renderBlock(node, defs) {
  switch (node.t) {
    case 'p':
      return '<p>' + parseInline(node.src, defs) + '</p>\n';
    case 'h':
      return '<h' + node.level + '>' + parseInline(node.src, defs) + '</h' + node.level + '>\n';
    case 'hr':
      return '<hr>\n';
    case 'code':
    case 'icode': {
      const info = node.t === 'code' && node.info ? ' class="language-' + escapeHtml(node.info, false) + '"' : '';
      return '<pre><code' + info + '>' + escapeHtml(node.src, true) + '</code></pre>\n';
    }
    case 'html':
      return node.src;
    case 'bq': {
      let out = '<blockquote>\n';
      for (const ch of node.children) out += renderBlock(ch, defs);
      return out + '</blockquote>\n';
    }
    case 'list': {
      const tag = node.kind === 'bullet' ? 'ul' : 'ol';
      let out = '<' + tag;
      if (node.kind === 'ordered' && node.start !== 1) out += ' start="' + node.start + '"';
      out += '>\n';
      for (const ch of node.children) out += renderBlock(ch, defs);
      return out + '</' + tag + '>\n';
    }
    case 'item': {
      const tight = node.parent && node.parent.tight;
      let out = '<li>';
      const kids = node.children;
      for (let idx = 0; idx < kids.length; idx++) {
        const ch = kids[idx];
        if (ch.t === 'p' && tight) {
          out += renderParaInItem(ch, defs, idx === 0);
        } else if (ch.t === 'p' && idx === 0) {
          out += '<p>' + renderParaInItem(ch, defs, true) + '</p>\n';
        } else {
          out += renderBlock(ch, defs);
        }
      }
      return out + '</li>\n';
    }
    case 'table': {
      let out = '<table>\n<thead>\n<tr>\n';
      for (let c = 0; c < node.head.length; c++) {
        const align = node.align[c];
        out += '<th' + (align ? ' align="' + align + '"' : '') + '>' + parseInline(node.head[c], defs) + '</th>\n';
      }
      out += '</tr>\n</thead>\n';
      if (node.rows.length > 0) {
        out += '<tbody>';
        for (const row of node.rows) {
          out += '<tr>\n';
          for (let c = 0; c < node.head.length; c++) {
            const cell = c < row.length ? trimCell(row[c]) : '';
            const align = node.align[c];
            out += '<td' + (align ? ' align="' + align + '"' : '') + '>' + parseInline(cell, defs) + '</td>\n';
          }
          out += '</tr>\n';
        }
        out += '</tbody>';
      }
      return out + '</table>\n';
    }
  }
  return '';
}
// Render a paragraph that is a list item's (first) child, handling the
// GFM task-list checkbox ([ ] / [x] / [X] + space) at its start.
function renderParaInItem(p, defs, isFirst) {
  if (isFirst) {
    const src = p.src;
    let k = 0;
    while (k < src.length && src.charCodeAt(k) === SP) k++;
    if (k + 2 < src.length && src.charCodeAt(k) === LBRACK) {
      const mark = src.charCodeAt(k + 1);
      if ((mark === SP || mark === 120 || mark === 88) && src.charCodeAt(k + 2) === RBRACK) {
        const after = k + 3 < src.length ? src.charCodeAt(k + 3) : -1;
        if (after === SP || after === TAB || after === -1) {
          const checked = mark !== SP;
          const box = checked
            ? '<input checked="" disabled="" type="checkbox">'
            : '<input disabled="" type="checkbox">';
          const restStart = (after === SP || after === TAB) ? k + 4 : k + 3;
          return box + ' ' + parseInline(src.slice(restStart), defs);
        }
      }
    }
  }
  return parseInline(p.src, defs);
}
export function parse(markdown) {
  const src = String(markdown).replace(/\r\n?/g, '\n');
  const { root, defs } = parseBlocks(src);
  let out = '';
  for (const child of root.children) out += renderBlock(child, defs);
  // A type 6-7 HTML block that is the last block in the document (and
  // did not end at a blank line) keeps the trailing newline of its last
  // line. (Types 1-5 already carry theirs from finalize.)
  if (src.length > 0 && src.charCodeAt(src.length - 1) === NL) {
    const n = lastLeaf(root);
    if (n.t === 'html' && n.htmlType >= 6 && !n.endedAtBlank) out += '\n';
  }
  return out;
}
