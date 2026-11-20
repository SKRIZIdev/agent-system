#!/usr/bin/env python3
"""Интера: граф внутренних ссылок статического сайта, квоты анкоров и аудит по norms.md.

usage:
  linkgraph.py init <site_dir> [--domain example.org]          заготовка targets.json в stdout
  linkgraph.py scan <site_dir> [--config targets.json] [--out DIR] [--packages]
  linkgraph.py diff <old_scan_dir> <new_scan_dir> [--config targets.json] [--focus /a/,/b/]

scan пишет в DIR (по умолчанию рядом с targets.json, иначе ~/intera-work/<сайт>/<дата-время>):
  graph.csv     все ссылки: донор, цель, зона, анкор, класс анкора, строка, контекст
  pages.csv     страницы: тип, индексируемость, знаков текста, исходящие/входящие, глубина
  findings.csv  нарушения ERR/WARN с адресом
  report.md     сводка по-русски; packages/*.md — постраничные пакеты по целям (--packages)
Только stdlib, Python 3.8+. Сайт не меняет.
"""
import argparse, csv, datetime, json, os, re, sys, unicodedata
from collections import Counter, defaultdict, deque
from html.parser import HTMLParser
from urllib.parse import unquote, urljoin, urlsplit

VOID = {'area', 'base', 'br', 'col', 'embed', 'hr', 'img', 'input', 'link', 'meta', 'source', 'track', 'wbr'}
SKIP_TEXT = {'script', 'style', 'noscript', 'template', 'svg', 'title'}
HEADINGS = {'h1', 'h2', 'h3', 'h4', 'h5', 'h6'}
BLOCKS = {'p', 'li', 'td', 'th', 'dd', 'dt', 'blockquote', 'figcaption', 'summary', 'caption', 'div', 'section',
          'article', 'aside', 'main', 'header', 'footer', 'nav', 'details', 'body', 'ul', 'ol', 'table'} | HEADINGS
TEXT_BLOCKS = {'p', 'li', 'td', 'th', 'dd', 'dt', 'blockquote'}
P_CLOSERS = {'p', 'div', 'ul', 'ol', 'table', 'section', 'article', 'aside', 'header', 'footer', 'nav', 'blockquote',
             'details', 'figure', 'form', 'pre', 'hr', 'main'} | HEADINGS
SKIP_DIRS = {'.git', 'node_modules', 'wp-json', 'wp-content', 'wp-includes', '__pycache__', '.wrangler'}
GENERIC = {
    'здесь', 'тут', 'сюда', 'по ссылке', 'подробнее', 'читать далее', 'читать', 'далее', 'ссылка', 'этот', 'эта', 'это',
    'here', 'click here', 'read more', 'more', 'this', 'link', 'this page', 'learn more', 'see more', 'details',
    'aquí', 'aqui', 'acá', 'leer más', 'ver más', 'más', 'mas', 'saiba mais', 'leia mais', 'clique aqui', 'veja mais',
    'tutaj', 'więcej', 'czytaj więcej', 'zde', 'více', 'tady', 'hier', 'mehr', 'weiterlesen', 'ici', 'plus', 'qui',
}
TLDS = ('com|org|net|ru|io|ai|app|co|info|biz|site|online|xyz|me|us|uk|eu|de|fr|it|es|pl|cz|sk|pt|br|mx|ar|cl|in|'
        'vn|ua|kz|by|ro|hu|nl|be|ch|at|se|no|fi|dk|tr|jp|kr|id|ph|th|ca|au|nz|za|pro|club|top|live|store|shop')
DOMAIN_RE = re.compile(r'\b[a-z0-9][a-z0-9-]*\.(?:%s)\b' % TLDS, re.I)
POLICY_RE = re.compile(r'privacy|polityka|privacidad|privacidade|terms|regulamin|terminos|termos|cookie|disclaimer|'
                       r'disclosure|legal|impressum|responsible|politica|aviso|conditions|gdpr|dmca|affiliate', re.I)
HERO_RE = r'hero|ph|page-head|page-header|jumbotron'
RELATED_RE = r'related|recommend|see-also|read-next|more-posts|also-read|similar'
SIDE_RE = r'sidebar|widget|side-cta|sticky|sticky-cta'
CRUMB_RE = r'crumbs?|breadcrumbs?'
TOC_RE = r'toc|table-of-contents'
HEADER_RE = r'topbar|masthead|site-header|navbar|header'
FOOTER_RE = r'site-footer|footer'
BUTTON_RE = r'btn|button|pill|cta'


def cls_re(alts):
    return re.compile(r'(?:^|[\s_-])(?:%s)(?:$|[\s_-])' % alts, re.I)


def norm(s):
    s = unicodedata.normalize('NFKC', s or '').replace('\xa0', ' ').lower()
    s = re.sub(r'\s+', ' ', s).strip()
    return s.strip(' .,:;!?«»"\'()[]{}—–-…→›')


def stems(s):
    return {t[:5] for t in re.findall(r'\w+', norm(s)) if len(t) >= 3}


def collapse(s):
    return re.sub(r'\s+', ' ', s.replace('\xa0', ' ')).strip()


# ---------------------------------------------------------------- parsing

class Page(HTMLParser):
    def __init__(self, src, opts):
        super().__init__(convert_charrefs=True)
        self.o = opts
        has_main = re.search(r'<main[\s>]', src, re.I) is not None
        self.stack = [{'tag': '#root', 'zone': 'layout' if has_main else 'content', 'block': None}]
        self.blocks = {}
        self.nblock = 0
        self.skip = 0
        self.links = []
        self.a = None
        self.chars = 0
        self.section = 0
        self.title = ''
        self.in_title = False
        self.h1 = []
        self.h1_buf = None
        self.noindex = False
        self.canonical = ''
        self.lang = ''

    # zone of a child element given the parent zone
    def zone_for(self, parent, tag, attrs):
        o = self.o
        c = ' '.join(filter(None, [attrs.get('class', ''), attrs.get('id', ''), attrs.get('aria-label', '')]))
        if o['crumb'].search(c):
            return 'crumbs'
        if o['toc'].search(c) and tag in ('nav', 'div', 'aside', 'ol', 'ul'):
            return 'toc'
        if parent not in ('content', 'layout'):
            return parent
        if tag == 'main':
            return 'content'
        inside_article = any(f['tag'] in ('article', 'section', 'main') for f in self.stack)
        if tag in ('header', 'footer') and not inside_article:
            return tag
        if tag == 'nav':
            return 'nav'
        if o['layout'] and o['layout'].search(c):
            return 'nav'
        if not inside_article and o['header'].search(c):
            return 'header'
        if not inside_article and o['footer'].search(c):
            return 'footer'
        if parent == 'layout':
            return 'layout'
        if tag in HEADINGS or tag == 'summary':
            return 'heading'
        if tag == 'figcaption':
            return 'caption'
        if o['hero'].search(c):
            return 'hero'
        if o['related'].search(c):
            return 'related'
        if o['side'].search(c):
            return 'aside'
        if tag == 'button':
            return 'button'
        return 'content'

    def cur(self):
        return self.stack[-1]

    def push(self, tag, attrs):
        parent = self.cur()
        frame = {'tag': tag, 'zone': self.zone_for(parent['zone'], tag, attrs), 'block': parent['block']}
        if tag in BLOCKS:
            self.nblock += 1
            b = {'id': self.nblock, 'tag': tag, 'buf': [], 'len': 0, 'links': [], 'parent': parent['block']}
            self.blocks[self.nblock] = b
            frame['block'] = self.nblock
        self.stack.append(frame)

    def pop_frame(self):
        f = self.stack.pop()
        if f['block'] is not None and f['block'] != self.stack[-1]['block']:
            self.close_block(self.blocks[f['block']])
        if f['tag'] in SKIP_TEXT:
            self.skip = max(0, self.skip - 1)
        if f['tag'] == 'h1' and self.h1_buf is not None:
            self.h1.append(collapse(''.join(self.h1_buf)))
            self.h1_buf = None

    def close_block(self, b):
        text = ''.join(b['buf'])
        for link, start, end in b['links']:
            link['context'] = context(text, start, end)
            link['sent'] = len(re.findall(r'[.!?…](?:\s|$)', text[:start]))
        if b['parent'] is not None:
            pb = self.blocks[b['parent']]
            pb['buf'].append(' ' + text + ' ')
            pb['len'] += len(text) + 2

    def handle_starttag(self, tag, attrs_list):
        attrs = {k: (v or '') for k, v in attrs_list}
        if tag == 'html':
            self.lang = attrs.get('lang', '')
        if tag == 'meta' and attrs.get('name', '').lower() == 'robots' and 'noindex' in attrs.get('content', '').lower():
            self.noindex = True
        if tag == 'link' and 'canonical' in attrs.get('rel', '').lower():
            self.canonical = attrs.get('href', '')
        if tag == 'title':
            self.in_title = True
        if tag == 'img' and self.a is not None:
            self.a['img'] = True
            self.a['alt'].append(attrs.get('alt', ''))
        if tag in VOID:
            return
        if tag in P_CLOSERS and self.cur()['tag'] == 'p':
            self.pop_frame()
        if tag == 'li' and self.cur()['tag'] == 'li':
            self.pop_frame()
        if tag in SKIP_TEXT:
            self.skip += 1
        if tag == 'h1':
            self.h1_buf = []
        if tag == 'h2':
            self.section += 1
        if self.a is not None:
            if tag in HEADINGS or tag in ('div', 'p', 'figure', 'ul', 'ol', 'table'):
                self.a['card'] = True
            if len(self.stack) == self.a_depth + 1 and tag in ('span', 'b', 'strong', 'small', 'em', 'i', 'div', 'p'):
                self.a['kids'] += 1
            if tag in ('div', 'p', 'span', 'li', 'small', 'br') or tag in HEADINGS:
                self.a['text'].append(' ')
        if tag == 'a' and 'href' in attrs and self.a is None:
            zone = self.cur()['zone']
            c = attrs.get('class', '')
            if zone == 'content' and self.o['button'].search(c):
                zone = 'button'
            b = self.blocks.get(self.cur()['block'])
            self.a = {'href': attrs['href'], 'zone': zone, 'text': [], 'alt': [], 'img': False, 'card': False, 'kids': 0,
                      'line': self.getpos()[0], 'block': b['id'] if b else 0, 'btag': b['tag'] if b else '',
                      'start': b['len'] if b else 0, 'pos': self.chars, 'context': '', 'rel': attrs.get('rel', ''),
                      'sec': self.section, 'sent': 0}
            self.a_block = b
            self.a_depth = len(self.stack)
        self.push(tag, attrs)

    def handle_startendtag(self, tag, attrs):
        self.handle_starttag(tag, attrs)
        if tag not in VOID:
            self.handle_endtag(tag)

    def handle_endtag(self, tag):
        if tag == 'title':
            self.in_title = False
        if tag in VOID or not any(f['tag'] == tag for f in self.stack[1:]):
            return
        while True:
            top = self.cur()['tag']
            if top == 'a' and self.a is not None and len(self.stack) == self.a_depth + 1:
                self.finish_a()
            self.pop_frame()
            if top == tag:
                break

    def finish_a(self):
        a = self.a
        self.a = None
        text = collapse(''.join(a['text']))
        a['anchor'] = text or collapse(' '.join(a['alt']))
        if a['zone'] == 'content' and (a['card'] or a['kids'] >= 2 or (a['img'] and not text)):
            a['zone'] = 'card'
        b = self.a_block
        if b is not None:
            b['links'].append((a, a['start'], b['len']))
        self.links.append(a)

    def handle_data(self, data):
        if self.in_title:
            self.title += data
        if self.skip:
            return
        if self.h1_buf is not None:
            self.h1_buf.append(data)
        if self.a is not None:
            self.a['text'].append(data)
        b = self.blocks.get(self.cur()['block'])
        if b is not None:
            b['buf'].append(data)
            b['len'] += len(data)
        if self.cur()['zone'] in ('content', 'heading'):
            self.chars += len(collapse(data))

    def finish(self):
        while len(self.stack) > 1:
            if self.cur()['tag'] == 'a' and self.a is not None:
                self.finish_a()
            self.pop_frame()


def context(text, start, end, limit=320):
    """Sentence(s) around the link, the anchor marked as [[...]]."""
    left = text[:start]
    m = list(re.finditer(r'[.!?…](?:\s|$)', left))
    s = m[-1].end() if m else 0
    m2 = re.search(r'[.!?…](?:\s|$)', text[end:])
    e = end + m2.end() if m2 else len(text)
    after = collapse(text[end:e])
    out = collapse(text[s:start]) + ' [[' + collapse(text[start:end]) + ']]' + ('' if after[:1] in ('', '.', ',', ';', ':', '!', '?', ')', '…') else ' ') + after
    out = collapse(out)
    return out if len(out) <= limit else out[:limit] + '…'


# ---------------------------------------------------------------- site model

def load_config(path):
    if not path:
        return {}
    with open(path, encoding='utf-8') as f:
        return json.load(f)


def options(cfg):
    def merged(default, key):
        extra = cfg.get(key) or []
        return cls_re('|'.join([default] + [re.escape(x) for x in extra])) if default or extra else None
    return {
        'hero': merged(HERO_RE, 'hero_classes'), 'related': merged(RELATED_RE, 'related_classes'),
        'side': merged(SIDE_RE, 'side_classes'), 'crumb': cls_re(CRUMB_RE), 'toc': cls_re(TOC_RE),
        'header': cls_re(HEADER_RE), 'footer': cls_re(FOOTER_RE), 'button': merged(BUTTON_RE, 'button_classes'),
        'layout': merged('', 'layout_classes'),
    }


def url_of(rel):
    rel = rel.replace(os.sep, '/')
    if rel == 'index.html':
        return '/'
    if rel.endswith('/index.html'):
        return '/' + rel[:-len('index.html')]
    return '/' + rel


def scan_site(root, cfg):
    opts = options(cfg)
    pages, url_map = {}, {}
    for d, dirs, files in os.walk(root):
        dirs[:] = sorted(x for x in dirs if x not in SKIP_DIRS and not x.startswith('.'))
        for fn in sorted(files):
            if not fn.endswith(('.html', '.htm')) or fn in ('404.html',) or re.match(r'(google|yandex_).*\.html$', fn):
                continue
            path = os.path.join(d, fn)
            u = url_of(os.path.relpath(path, root))
            with open(path, encoding='utf-8', errors='replace') as f:
                src = f.read()
            p = Page(src, opts)
            try:
                p.feed(src)
                p.close()
            except Exception as e:  # broken markup: keep what was parsed
                print('! парсер споткнулся на %s: %s' % (u, e), file=sys.stderr)
            p.finish()
            pages[u] = {'url': u, 'file': os.path.relpath(path, root), 'title': collapse(p.title),
                        'h1': p.h1[0] if p.h1 else '', 'h1_count': len(p.h1), 'noindex': p.noindex,
                        'canonical': p.canonical, 'chars': p.chars, 'lang': p.lang, 'links': p.links, 'sections': p.section}
            variants = [u]
            if u.endswith('/'):
                variants += [u + 'index.html', u.rstrip('/') or '/']
            elif u.endswith(('.html', '.htm')):
                variants.append(re.sub(r'\.html?$', '', u))
            for v in variants:
                url_map.setdefault(v, u)
    return pages, url_map


def site_hosts(cfg, pages):
    hosts = set(h.lower() for h in (cfg.get('domain') or []))
    if isinstance(cfg.get('domain'), str):
        hosts = {cfg['domain'].lower()}
    for p in pages.values():
        if p['canonical'].startswith('http'):
            hosts.add(urlsplit(p['canonical']).netloc.lower())
    hosts |= {'www.' + h for h in list(hosts) if not h.startswith('www.')}
    hosts |= {h[4:] for h in list(hosts) if h.startswith('www.')}
    return hosts


def resolve(href, donor, url_map, hosts, ignore):
    href = (href or '').strip()
    if not href or href.startswith(('#', 'mailto:', 'tel:', 'javascript:', 'data:', 'sms:', 'viber:', 'whatsapp:')):
        return 'skip', None
    p = urlsplit(urljoin('https://site.invalid' + donor, href))
    if p.scheme not in ('http', 'https'):
        return 'skip', None
    host = p.netloc.lower()
    if host != 'site.invalid' and host not in hosts:
        return 'external', href
    path = unquote(p.path) or '/'
    if any(path.startswith(ig) for ig in ignore):
        return 'ignored', path
    ext = os.path.splitext(path)[1].lower()
    if ext and ext not in ('.html', '.htm', '.php'):
        return 'asset', path
    for cand in (path, path + '/', path.rstrip('/') + '.html', path.rstrip('/') + '/index.html'):
        if cand in url_map:
            return 'page', url_map[cand]
    return 'broken', path


def lang_roots(pages, cfg):
    """Language homes (/br/, /de/...) from config or detected: 1st-level dir, lang code name, own <html lang>."""
    if cfg.get('lang_roots') is not None:
        return set(cfg['lang_roots']) | ({'/'} if '/' in pages else set())
    root_lang = (pages.get('/') or {}).get('lang', '').lower()
    roots = {'/'} if '/' in pages else set()
    for u, p in pages.items():
        if re.fullmatch(r'/[a-z]{2}(?:-[a-z]{2})?/', u, re.I) and p['lang'] and p['lang'].lower() != root_lang:
            roots.add(u)
    return roots


def page_type(u, cfg, roots=('/',)):
    t = (cfg.get('targets') or {}).get(u, {}).get('type')
    if t:
        return t
    if u in roots:
        return 'home'
    if u in (cfg.get('policy') or []) or (cfg.get('policy') is None and POLICY_RE.search(u)):
        return 'policy'
    return 'info'


def classify(anchor, target, cfg, home):
    a = norm(anchor)
    if not a:
        return 'empty'
    if a in GENERIC:
        return 'generic'
    if a.startswith(('http://', 'https://', 'www.')) or DOMAIN_RE.search(a):
        return 'url'
    brands = {norm(b) for b in cfg.get('brand') or []}
    tcfg = (cfg.get('targets') or {}).get(target, {})
    exact = tcfg.get('exact') or []
    exact = [exact] if isinstance(exact, str) else exact
    exact_n = {norm(x) for x in exact if x}
    if a in exact_n:
        return 'exact'
    if a in brands:
        return 'brand'
    if a in {norm(x) for x in tcfg.get('lsi') or []}:
        return 'lsi'
    for x in exact_n:
        st = stems(x)
        if x in a or (st and len(st & stems(a)) / len(st) >= 0.5):
            return 'partial'
    if not exact_n:
        return 'n/a'
    return 'descriptive'


def words(anchor):
    return len(norm(anchor).split())


def anchor_len_issue(anchor, target, cfg):
    """None if fine, else (severity, message). 1–2 words; 3–4 only as a listed key of this target; 5+ never."""
    aw = cfg.get('anchor_words') or {}
    mx, key_mx = aw.get('max', 2), aw.get('key_max', 4)
    n = words(anchor)
    if n <= mx:
        return None
    if n > key_mx:
        return 'ERR', '%d слов — это фраза, а не анкор (норма 1–%d)' % (n, mx)
    tcfg = (cfg.get('targets') or {}).get(target, {})
    ex = tcfg.get('exact') or []
    keys = {norm(x) for x in ([ex] if isinstance(ex, str) else ex) + list(tcfg.get('lsi') or []) if x}
    if norm(anchor) in keys:
        return None
    if keys:
        return 'ERR', '%d слова, а такого ключа нет в анкор-листе цели (норма 1–%d)' % (n, mx)
    return 'WARN', '%d слова при норме 1–%d; длиннее — только ключ из анкор-листа (exact/LSI не заданы)' % (n, mx)


def exact_range(total, kind, cfg):
    """(min, max) exact anchors on a target: min 3 (or all if <3), ceiling max(3, 10%) — norms §4, owner decision 2026-11-12 (was 5)."""
    if kind == 'home':
        share = (cfg.get('home_quota') or {}).get('exact_share', 0.35)
        return min(total, (cfg.get('home_quota') or {}).get('exact_min', max(1, round(total * share)))), total
    # потолок: money/category — 3 (норма 12.11), остальные цели (hub/info/policy) — как раньше, 5
    hi = max(3 if kind in ('money', 'category') else 5, int(total * 0.10))
    lo = min(3, total) if kind in ('money', 'category') else 0
    return lo, hi


# ---------------------------------------------------------------- analysis

def analyse(root, cfg):
    pages, url_map = scan_site(root, cfg)
    hosts = site_hosts(cfg, pages)
    ignore = cfg.get('ignore') or ['/go/', '/cdn-cgi/', '/wp-json/', '/out/', '/recommends/']
    skip_pages = set(cfg.get('skip_pages') or ['/sitemap/', '/sitemap.html', '/html-sitemap/', '/site-map/'])
    home = '/' if '/' in pages else None
    roots = lang_roots(pages, cfg)

    def home_of(u):
        return max((r for r in roots if u.startswith(r)), key=len, default=home)
    home_links = cfg.get('home_links') or {'min': 1, 'max': 1}
    dens = cfg.get('density') or {}
    dense, sparse = dens.get('chars_per_link', [400, 650])   # 1 link per 400 chars = upper bound, per 650 = lower
    cap = dens.get('cap', 10)
    rows, findings = [], []

    def F(sev, page, line, code, msg):
        findings.append({'sev': sev, 'page': page, 'line': line, 'code': code, 'msg': msg})

    for u, p in pages.items():
        p['type'] = page_type(u, cfg, roots)
        can = p['canonical']
        can_ok = True
        if can:
            k, t = resolve(can, u, url_map, hosts | {'site.invalid'}, [])
            can_ok = (k == 'page' and t == u)
        p['indexable'] = (not p['noindex']) and can_ok
        for a in p['links']:
            kind, target = resolve(a['href'], u, url_map, hosts, ignore)
            a['kind'], a['target'] = kind, target
            if kind == 'page':
                a['class'] = classify(a['anchor'], target, cfg, home) if a['zone'] == 'content' else ''
            else:
                a['class'] = ''
            if kind in ('page', 'broken'):
                rows.append({'donor': u, 'target': target, 'zone': a['zone'], 'anchor': a['anchor'],
                             'class': a['class'], 'line': a['line'], 'block': '%s#%s' % (a['btag'], a['block']),
                             'context': a['context'], 'kind': kind, 'sec': a['sec'],
                             'sent': '%s#%s.%s' % (a['btag'], a['block'], a['sent'])})
            if kind == 'broken':
                F('ERR', u, a['line'], 'broken', 'битая внутренняя ссылка %s (зона %s)' % (a['href'], a['zone']))

    content = [r for r in rows if r['kind'] == 'page' and r['zone'] == 'content']
    by_target = defaultdict(list)
    for r in content:
        if r['donor'] != r['target']:
            by_target[r['target']].append(r)

    # click depth over every link, all zones
    adj = defaultdict(set)
    for r in rows:
        if r['kind'] == 'page':
            adj[r['donor']].add(r['target'])
    depth = {r: 0 for r in roots}
    if roots:
        q = deque(sorted(roots))
        while q:
            x = q.popleft()
            for y in adj[x]:
                if y not in depth:
                    depth[y] = depth[x] + 1
                    q.append(y)

    indexable = [u for u, p in pages.items() if p['indexable']]
    content_pages = [u for u in indexable if pages[u]['type'] not in ('policy',) and u not in skip_pages]
    min_in = min(3, max(0, len(content_pages) - 1))

    # ---- per target (incoming)
    tstats = {}
    for u in pages:
        p = pages[u]
        inc = by_target.get(u, [])
        donors = sorted({r['donor'] for r in inc})
        cls = Counter(r['class'] for r in inc)
        tot = len(inc)
        st = {'in': tot, 'donors': len(donors), 'exact': cls.get('exact', 0), 'classes': dict(cls),
              'depth': depth.get(u), 'top': Counter(norm(r['anchor']) for r in inc).most_common(5)}
        tstats[u] = st
        if not p['indexable']:
            continue
        if u not in roots and depth.get(u) is None:
            F('ERR', u, 0, 'unreachable', 'недостижима с главной ни по одной ссылке')
        elif p['type'] in ('money', 'category') and depth[u] > 2:
            F('ERR', u, 0, 'depth', 'money-страница в %d кликах от главной, норма ≤2' % depth[u])
        elif depth.get(u) is not None and depth[u] > 3:
            F('WARN', u, 0, 'depth', 'глубина %d клика' % depth[u])
        if u not in roots and p['type'] != 'policy' and u not in skip_pages and st['donors'] < min_in:
            F('ERR', u, 0, 'few_incoming', 'входящих content-ссылок с разных страниц %d, норма ≥%d' % (st['donors'], min_in))
        if p['type'] == 'policy' and st['donors'] > 30:
            F('ERR', u, 0, 'policy_donors', 'policy: %d content-доноров, норма ≤30' % st['donors'])
        tcfg = (cfg.get('targets') or {}).get(u, {})
        if tcfg.get('exact') and tot:
            lo, hi = exact_range(tot, p['type'], cfg)
            st['exact_norm'] = '%d–%d' % (lo, hi) if hi != tot else '≥%d' % lo
            if st['exact'] < lo:
                F('ERR' if p['type'] != 'home' else 'WARN', u, 0, 'exact_low',
                  'exact %d из %d, норма %s' % (st['exact'], tot, st['exact_norm']))
            if st['exact'] > hi:
                F('ERR', u, 0, 'exact_high', 'exact %d из %d (%d%%), норма %s' % (
                    st['exact'], tot, 100 * st['exact'] // tot, st['exact_norm']))
        if tot >= 5:
            reps = Counter((norm(r['anchor']), r['class']) for r in inc if r['class'] in ('lsi', 'partial', 'descriptive', 'n/a'))
            limit = max(1, int(tot * 0.2))
            for (anc, c), n in reps.most_common():
                if n > limit:
                    F('ERR' if c != 'n/a' else 'WARN', u, 0, 'partial_repeat' if c != 'n/a' else 'anchor_repeat',
                      'анкор «%s» повторён %d раз из %d, норма ≤%d (20%%)' % (anc, n, tot, limit))

    # ---- site-wide anchor rules
    brands = {norm(b) for b in cfg.get('brand') or []}
    exact_owner = {}
    for t, tc in (cfg.get('targets') or {}).items():
        ex = tc.get('exact') or []
        for x in ([ex] if isinstance(ex, str) else ex):
            if x:
                exact_owner[norm(x)] = t
    anchor_targets = defaultdict(set)
    forbidden = [norm(w) for w in cfg.get('forbidden') or [] if w]
    for r in rows:
        bad = [w for w in forbidden if re.search(r'(?<!\w)%s' % re.escape(w), norm(r['anchor']))]
        if bad and r['kind'] == 'page':
            F('ERR', r['donor'], r['line'], 'forbidden', 'запрещённое слово «%s» в анкоре «%s» → %s' % (bad[0], r['anchor'], r['target']))
    for r in content:
        a = norm(r['anchor'])
        if r['class'] not in ('generic', 'url', 'empty') and a:
            anchor_targets[a].add(r['target'])
        if a in brands and r['target'] not in roots:
            F('ERR', r['donor'], r['line'], 'brand_not_home', 'бренд-анкор «%s» ведёт на %s, бренд — только на главную' % (r['anchor'], r['target']))
        if r['class'] in ('generic', 'url', 'empty'):
            F('ERR', r['donor'], r['line'], 'bad_anchor', 'анкор «%s» (%s) → %s' % (r['anchor'], r['class'], r['target']))
        long_ = anchor_len_issue(r['anchor'], r['target'], cfg) if r['class'] not in ('generic', 'url', 'empty') else None
        if long_:
            F(long_[0], r['donor'], r['line'], 'anchor_long', '«%s» → %s: %s' % (r['anchor'], r['target'], long_[1]))
        if a in exact_owner and exact_owner[a] != r['target']:
            F('ERR', r['donor'], r['line'], 'cannibal', 'exact «%s» принадлежит %s, а ведёт на %s' % (r['anchor'], exact_owner[a], r['target']))
    for a, ts in anchor_targets.items():
        if len(ts) > 1 and a not in exact_owner and len(a.split()) >= 2:
            F('WARN', '*', 0, 'same_anchor', 'анкор «%s» ведёт на %d разных URL: %s' % (a, len(ts), ', '.join(sorted(ts))))

    # ---- per donor (outgoing)
    dstats = {}
    for u, p in pages.items():
        out = [r for r in content if r['donor'] == u]
        h = home_of(u)
        internal = [r for r in out if r['target'] not in (u, h)]
        to_home = [r for r in out if r['target'] == h and u != h]
        lo = min(dens.get('long_min', 6), cap, max(1, p['chars'] // sparse))
        hi = min(cap, -(-p['chars'] // dense))
        dstats[u] = {'out': len({r['target'] for r in internal}), 'home': len(to_home), 'norm': '%d–%d' % (lo, hi)}
        allz = [a for a in p['links'] if a['kind'] == 'page']
        if not p['indexable'] or u in skip_pages:
            continue
        for a in allz:
            if a['zone'] == 'heading':
                F('ERR', u, a['line'], 'in_heading', 'ссылка из заголовка → %s «%s»' % (a['target'], a['anchor']))
            if a['zone'] == 'hero' and a['target'] != u and pages[a['target']]['type'] != 'policy':
                F('ERR', u, a['line'], 'in_hero', 'ссылка в hero → %s «%s»' % (a['target'], a['anchor']))
            if a['zone'] == 'caption':
                F('WARN', u, a['line'], 'in_caption', 'ссылка в подписи к картинке → %s «%s»' % (a['target'], a['anchor']))
        for r in out:
            if r['target'] == u:
                F('ERR', u, r['line'], 'self', 'self-ссылка в тексте «%s»' % r['anchor'])
            elif r['target'] in pages and not pages[r['target']]['indexable']:
                F('WARN', u, r['line'], 'to_noindex', 'ссылка из текста на неиндексируемую %s' % r['target'])
        if u in roots:
            continue
        if p['type'] != 'policy':
            parts = [('', to_home, home_links)]
            if 'brand' in home_links or 'other' in home_links:
                parts = [(' бренд', [r for r in to_home if norm(r['anchor']) in brands], home_links.get('brand') or {}),
                         (' не бренд', [r for r in to_home if norm(r['anchor']) not in brands], home_links.get('other') or {})]
            for label, got, q in parts:
                if not q:
                    continue
                q_min, q_max = q.get('min', 0), q.get('max', 99)
                if not (q_min <= len(got) <= q_max):
                    F('ERR', u, got[0]['line'] if got else 0, 'home_links',
                      'ссылок на главную %s%s из текста %d, норма %s' % (
                          h, label, len(got), q_min if q_min == q_max else '%d–%d' % (q_min, q_max)))
        cnt = Counter(r['target'] for r in internal)
        for t, n in cnt.items():
            if n > 1:
                lines = [r['line'] for r in internal if r['target'] == t]
                F('ERR', u, lines[1], 'duplicate', '%d ссылки на %s со страницы (строки %s), норма 1' % (n, t, ', '.join(map(str, lines))))
        if p['type'] != 'policy':
            n = len(cnt)
            if n > cap:
                F('ERR', u, 0, 'density_cap', 'внутренних ссылок в тексте %d, потолок %d' % (n, cap))
            elif n < lo:
                F('WARN', u, 0, 'density_low', 'внутренних ссылок в тексте %d при %d знаках, норма %s' % (n, p['chars'], dstats[u]['norm']))
            elif n > hi:
                F('WARN', u, 0, 'density_high', 'внутренних ссылок в тексте %d при %d знаках, норма %s' % (n, p['chars'], dstats[u]['norm']))
        site_links = [r for r in out if r['target'] != u]
        per_sent = Counter(r['sent'] for r in site_links)
        for snt, n in per_sent.items():
            if n > 1:
                F('ERR', u, min(r['line'] for r in site_links if r['sent'] == snt), 'cluster_sentence',
                  '%d ссылки в одном предложении: %s' % (n, ', '.join('«%s»' % r['anchor'] for r in site_links if r['sent'] == snt)))
        per_block = Counter(r['block'] for r in site_links if r['block'].split('#')[0] in TEXT_BLOCKS)
        for b, n in per_block.items():
            if n > 1 and per_sent.get(next(r['sent'] for r in site_links if r['block'] == b)) != n:
                F('ERR', u, min(r['line'] for r in site_links if r['block'] == b), 'cluster_block',
                  '%d ссылки в одном абзаце/пункте <%s>' % (n, b.split('#')[0]))
        secs = Counter(r['sec'] for r in site_links)
        if len(site_links) >= 4 and p.get('sections', 0) >= 3 and secs and secs.most_common(1)[0][1] > len(site_links) / 2:
            F('WARN', u, 0, 'cluster_section', '%d из %d ссылок в одном разделе (h2 №%s)' % (
                secs.most_common(1)[0][1], len(site_links), secs.most_common(1)[0][0]))
        poss = [a['pos'] for a in p['links'] if a['zone'] == 'content' and a['kind'] == 'page' and a['target'] != u]
        if len(poss) >= 3 and p['chars'] and min(poss) > 0.75 * p['chars']:
            F('WARN', u, 0, 'cluster_end', 'все %d ссылок в последней четверти текста' % len(poss))

    return pages, rows, findings, tstats, dstats, depth, home, roots


# ---------------------------------------------------------------- output

def write_csv(path, rows, fields):
    with open(path, 'w', newline='', encoding='utf-8') as f:
        w = csv.DictWriter(f, fieldnames=fields, extrasaction='ignore')
        w.writeheader()
        w.writerows(rows)


def default_out(site):
    site = os.path.abspath(site)
    name = os.path.basename(site)
    if name in ('dist', 'site', 'public', 'build', '_site', 'out', 'www', 'html', 'public_html', 'src'):
        name = os.path.basename(os.path.dirname(site)) + '-' + name
    return os.path.join(os.path.expanduser('~/intera-work'), name, datetime.datetime.now().strftime('%Y-%m-%d-%H%M'))


def cmd_scan(args):
    cfg = load_config(args.config)
    pages, rows, findings, tstats, dstats, depth, home, roots = analyse(args.site, cfg)
    out = args.out or (os.path.join(os.path.dirname(os.path.abspath(args.config)), datetime.datetime.now().strftime('%Y-%m-%d-%H%M'))
                       if args.config else default_out(args.site))
    os.makedirs(out, exist_ok=True)
    write_csv(os.path.join(out, 'graph.csv'), rows, ['donor', 'target', 'zone', 'anchor', 'class', 'line', 'block', 'sent', 'sec', 'kind', 'context'])
    prow = []
    for u, p in sorted(pages.items()):
        t, d = tstats[u], dstats[u]
        prow.append({'url': u, 'file': p['file'], 'type': p['type'], 'indexable': int(p['indexable']), 'chars': p['chars'],
                     'out_internal': d['out'], 'out_norm': d['norm'], 'to_home': d['home'], 'in_content': t['in'],
                     'in_donors': t['donors'], 'exact_in': t['exact'], 'depth': '' if t['depth'] is None else t['depth'],
                     'h1': p['h1'], 'title': p['title']})
    write_csv(os.path.join(out, 'pages.csv'), prow, list(prow[0].keys()) if prow else ['url'])
    findings.sort(key=lambda f: (f['sev'] != 'ERR', f['page'], f['line']))
    write_csv(os.path.join(out, 'findings.csv'), findings, ['sev', 'page', 'line', 'code', 'msg'])
    rep = report(args.site, cfg, pages, rows, findings, tstats, dstats, roots)
    with open(os.path.join(out, 'report.md'), 'w', encoding='utf-8') as f:
        f.write(rep)
    with open(os.path.join(out, 'meta.json'), 'w', encoding='utf-8') as f:
        json.dump({'site': os.path.abspath(args.site), 'config': os.path.abspath(args.config) if args.config else None,
                   'time': datetime.datetime.now().isoformat(timespec='seconds')}, f, ensure_ascii=False, indent=1)
    if args.packages:
        packages(out, cfg, pages, rows, tstats, dstats, roots)
    print(rep if not args.quiet else rep.split('\n## ')[0])
    print('\n→ %s' % out)


def report(site, cfg, pages, rows, findings, tstats, dstats, roots):
    idx = [u for u, p in pages.items() if p['indexable']]
    content = [r for r in rows if r['zone'] == 'content' and r['kind'] == 'page']
    zones = Counter(r['zone'] for r in rows if r['kind'] == 'page')
    errs = [f for f in findings if f['sev'] == 'ERR']
    warns = [f for f in findings if f['sev'] == 'WARN']
    L = ['# Перелинковка: %s' % os.path.abspath(site), '',
         'Страниц %d, индексируемых %d. Ссылок на страницы сайта %d, из них в тексте %d (зоны: %s).' % (
             len(pages), len(idx), sum(zones.values()), len(content), ', '.join('%s %d' % kv for kv in zones.most_common())),
         'Конфиг: %s. Главные: %s. **ERR %d · WARN %d**' % ('есть' if cfg else 'нет (анкоры не классифицированы)',
                                                       ' '.join(sorted(roots)), len(errs), len(warns)), '']
    groups = defaultdict(list)
    for f in findings:
        groups[(f['sev'], f['code'])].append(f)
    if findings:
        L.append('## Нарушения')
        for (sev, code), fs in sorted(groups.items(), key=lambda kv: (kv[0][0] != 'ERR', -len(kv[1]))):
            L.append('### %s %s — %d' % (sev, code, len(fs)))
            for f in fs[:40]:
                L.append('- `%s%s` — %s' % (f['page'], ':%s' % f['line'] if f['line'] else '', f['msg']))
            if len(fs) > 40:
                L.append('- … ещё %d (findings.csv)' % (len(fs) - 40))
        L.append('')
    L += ['## Цели (входящие из текста)', '', '| URL | тип | глубина | ссылок | доноров | exact | норма exact | частые анкоры |', '|---|---|---|---|---|---|---|---|']
    for u in sorted(pages, key=lambda x: (x not in roots, -tstats[x]['in'])):
        p, t = pages[u], tstats[u]
        if not p['indexable']:
            continue
        top = '; '.join('%s ×%d' % (a or '∅', n) for a, n in t['top'][:3])
        L.append('| %s | %s | %s | %d | %d | %d | %s | %s |' % (u, p['type'], '—' if t['depth'] is None else t['depth'], t['in'],
                                                               t['donors'], t['exact'], t.get('exact_norm', ''), top.replace('|', '/')))
    L += ['', '## Доноры (исходящие из текста)', '', '| URL | знаков | внутренних | норма | на главную |', '|---|---|---|---|---|']
    for u in sorted(pages):
        p, d = pages[u], dstats[u]
        if p['indexable'] and u not in roots and u not in (cfg.get('skip_pages') or ['/sitemap/']):
            L.append('| %s | %d | %d | %s | %d |' % (u, p['chars'], d['out'], d['norm'], d['home']))
    return '\n'.join(L) + '\n'


def packages(out, cfg, pages, rows, tstats, dstats, roots):
    pdir = os.path.join(out, 'packages')
    os.makedirs(pdir, exist_ok=True)
    targets = cfg.get('targets') or {}
    if not targets:
        targets = {u: {} for u, p in pages.items() if p['indexable'] and p['type'] in ('home', 'money', 'category', 'hub', 'policy')}
    content = [r for r in rows if r['zone'] == 'content' and r['kind'] == 'page']
    made = []
    for t, tc in targets.items():
        if t not in pages:
            print('! цели %s нет среди страниц' % t, file=sys.stderr)
            continue
        p, st = pages[t], tstats[t]
        inc = [r for r in content if r['target'] == t and r['donor'] != t]
        ex = tc.get('exact') or []
        ex = [ex] if isinstance(ex, str) else ex
        lo, hi = exact_range(len(inc), p['type'], cfg) if ex else (0, len(inc))
        seen, kept_exact, reps = set(), 0, Counter()
        limit = max(1, int(len(inc) * 0.2))
        for r in inc:
            key = r['donor']
            a = norm(r['anchor'])
            if key in seen:
                r['_status'] = 'DUPLICATE → удалить'
                continue
            seen.add(key)
            if r['class'] in ('generic', 'url', 'empty') or (r['class'] == 'brand' and t not in roots):
                r['_status'] = 'REWRITE_CONTEXT'
            elif anchor_len_issue(r['anchor'], t, cfg):
                r['_status'] = 'REWRITE_CONTEXT → короткий анкор (1–2 слова или ключ из листа)'
            elif r['class'] == 'exact':
                kept_exact += 1
                r['_status'] = 'KEEP' if kept_exact <= hi else 'REWRITE_CONTEXT → LSI'
            elif r['class'] in ('lsi', 'partial', 'descriptive', 'n/a'):
                reps[a] += 1
                r['_status'] = 'KEEP' if reps[a] <= limit or len(inc) < 5 else 'REWRITE_CONTEXT → другой LSI'
            else:
                r['_status'] = 'KEEP'
        if p['type'] == 'policy' and len(seen) > 30:
            for r in inc:
                if r['_status'] == 'KEEP':
                    r['_status'] = 'REVIEW (≤30: KEEP по ролям / CUT)'
        linked = {r['donor'] for r in inc}
        skip = set(cfg.get('skip_pages') or ['/sitemap/'])
        cands = sorted([u for u, q in pages.items() if q['indexable'] and u not in linked and u != t and q['type'] != 'policy' and u not in skip],
                       key=lambda u: -pages[u]['chars'])
        slug = t.strip('/').replace('/', '_') or 'home'
        L = ['# Пакет: %s (%s)' % (t, p['type']), '',
             '- H1: %s' % p['h1'], '- exact: %s' % (', '.join(ex) or '— (не задан в targets.json)'),
             '- LSI-пул: %s' % ('; '.join(tc.get('lsi') or []) or '— (собрать 8–12 из GSC / карты ключей)'),
             '- Сейчас: %d ссылок из текста с %d доноров; exact %d; норма exact %s; глубина %s' % (
                 len(inc), st['donors'], st['exact'], ('%d–%d' % (lo, hi)) if ex else '—', st['depth']),
             '- Задача: %s' % '; '.join(task(len(inc), st, lo, hi, ex, tc, p['type'], min_in(pages, cfg), len(seen))),
             '- Статусы ниже — предложение скрипта. BLOCKED_CONTEXT ставит Интера руками, когда контекст не позволяет.', '',
             '## Доноры (%d)' % len(inc), '']
        for i, r in enumerate(inc, 1):
            L.append('### %d. %s:%s — %s — **%s**' % (i, r['donor'], r['line'], r['class'] or 'n/a', r['_status']))
            L.append('> %s' % (r['context'] or '«%s»' % r['anchor']))
            L.append('')
        L += ['## Кандидаты в новые доноры (ещё не ссылаются из текста)', '', '| донор | знаков | внутренних сейчас / норма |', '|---|---|---|']
        for u in cands[:25]:
            L.append('| %s | %d | %d / %s |' % (u, pages[u]['chars'], dstats[u]['out'], dstats[u]['norm']))
        with open(os.path.join(pdir, slug + '.md'), 'w', encoding='utf-8') as f:
            f.write('\n'.join(L) + '\n')
        made.append(slug)
    print('пакеты: %s/{%s}.md' % (pdir, ','.join(made)), file=sys.stderr)


def min_in(pages, cfg):
    skip = set(cfg.get('skip_pages') or ['/sitemap/'])
    n = len([u for u, p in pages.items() if p['indexable'] and p['type'] != 'policy' and u not in skip])
    return min(3, max(0, n - 1))


def task(total, st, lo, hi, ex, tc, kind, need_in, donors):
    out = []
    if kind == 'policy':
        out.append('доноров %d, норма ≤30' % donors + (' → сократить' if donors > 30 else ' — в норме'))
        return out
    if kind != 'home' and donors < need_in:
        out.append('добавить доноров: +%d до %d' % (need_in - donors, need_in))
    if ex:
        if st['exact'] < lo:
            out.append('exact %d → поднять до %d (переписать анкор у KEEP-доноров или добавить доноров)' % (st['exact'], lo))
        elif st['exact'] > hi:
            out.append('exact %d → оставить %d, остальные в LSI' % (st['exact'], hi))
        else:
            out.append('exact в норме (%d)' % st['exact'])
    else:
        out.append('задать exact в targets.json по GSC/карте ключей')
    pool = len(tc.get('lsi') or [])
    if pool < 8:
        out.append('LSI-пул %d — добрать до 8–12 из GSC/карты ключей' % pool)
    return out or ['в норме']


def cmd_diff(args):
    def outside(d):
        with open(os.path.join(d, 'graph.csv'), encoding='utf-8') as f:
            return Counter((r['donor'], r['target'], r['zone'], norm(r['anchor'])) for r in csv.DictReader(f)
                           if r['zone'] != 'content' and r['kind'] == 'page')

    def load(d):
        with open(os.path.join(d, 'graph.csv'), encoding='utf-8') as f:
            rows = [r for r in csv.DictReader(f) if r['zone'] == 'content' and r['kind'] == 'page']
        m = defaultdict(list)
        for r in rows:
            m[(r['donor'], r['target'])].append(r['anchor'])
        return m
    old, new = load(args.old), load(args.new)
    cfg = load_config(args.config)
    focus = set(x for x in (args.focus or '').split(',') if x)
    approved = cfg.get('approved_donors') or {}
    added, removed, changed = [], [], []
    for k in sorted(set(old) | set(new)):
        a, b = old.get(k, []), new.get(k, [])
        if a and not b:
            removed.append((k, a))
        elif b and not a:
            added.append((k, b))
        elif sorted(map(norm, a)) != sorted(map(norm, b)):
            changed.append((k, a, b))
    per = defaultdict(lambda: [0, 0])
    for k in old:
        per[k[1]][0] += len(old[k])
    for k in new:
        per[k[1]][1] += len(new[k])
    L = ['# Diff перелинковки', '%s → %s' % (args.old, args.new), '',
         'Добавлено пар %d, удалено %d, анкор изменён %d.' % (len(added), len(removed), len(changed)), '',
         '| цель | было | стало |', '|---|---|---|']
    for t in sorted(per):
        if per[t][0] != per[t][1]:
            L.append('| %s | %d | %d |' % (t, per[t][0], per[t][1]))
    warn = []
    for title, items in (('Добавлено', added), ('Удалено', removed)):
        L += ['', '## ' + title]
        for (d, t), anchors in items:
            L.append('- %s → %s «%s»' % (d, t, '» «'.join(anchors)))
            if focus and t not in focus:
                warn.append('вне фокуса: %s %s → %s' % (title.lower(), d, t))
            if title == 'Добавлено' and t in approved and d not in approved[t]:
                warn.append('донор не утверждён: %s → %s' % (d, t))
    L += ['', '## Анкор изменён']
    for (d, t), a, b in changed:
        L.append('- %s → %s: «%s» → «%s»' % (d, t, '» «'.join(a), '» «'.join(b)))
        if focus and t not in focus:
            warn.append('вне фокуса: изменён анкор %s → %s' % (d, t))
    extra = outside(args.new) - outside(args.old)
    for (d, t, z, a), n in sorted(extra.items()):
        warn.append('ссылка добавлена вне текста (зона %s): %s → %s «%s»' % (z, d, t, a))
    if warn:
        L += ['', '## ⚠ Проверить'] + ['- ' + w for w in warn]
    print('\n'.join(L))


def cmd_init(args):
    cfg = {'domain': [args.domain] if args.domain else []}
    pages, _ = scan_site(args.site, cfg)
    targets = {}
    for u, p in sorted(pages.items()):
        if p['noindex'] or u in ('/sitemap/', '/sitemap.html', '/html-sitemap/', '/site-map/'):
            continue
        targets[u] = {'type': page_type(u, {}, lang_roots(pages, {})), 'exact': '', 'lsi': [], '_h1': p['h1'], '_title': p['title']}
    out = {'domain': cfg['domain'] or sorted(site_hosts({}, pages)), 'brand': [], 'ignore': ['/go/', '/cdn-cgi/', '/wp-json/'],
           'home_links': {'min': 1, 'max': 1}, 'home_quota': {'exact_share': 0.35},
           'density': {'chars_per_link': [400, 650], 'cap': 10, 'long_min': 6}, 'anchor_words': {'max': 2, 'key_max': 4},
           'skip_pages': ['/sitemap/'],
           'lang_roots': None, 'layout_classes': [], 'hero_classes': [], 'related_classes': [], 'policy': None,
           'forbidden': [], 'targets': targets, 'approved_donors': {}}
    print(json.dumps(out, ensure_ascii=False, indent=2))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest='cmd', required=True)
    s = sub.add_parser('scan')
    s.add_argument('site')
    s.add_argument('--config')
    s.add_argument('--out')
    s.add_argument('--packages', action='store_true')
    s.add_argument('--quiet', action='store_true', help='в stdout только сводка')
    d = sub.add_parser('diff')
    d.add_argument('old')
    d.add_argument('new')
    d.add_argument('--config')
    d.add_argument('--focus')
    i = sub.add_parser('init')
    i.add_argument('site')
    i.add_argument('--domain')
    a = ap.parse_args()
    {'scan': cmd_scan, 'diff': cmd_diff, 'init': cmd_init}[a.cmd](a)


if __name__ == '__main__':
    main()
