/* Sudoku-Engine: Generator, Löser, Schwierigkeitsbewertung, Hinweise */
(function (root) {
  const ALL = 0x1ff;
  const bit = (d) => 1 << (d - 1);
  const pop = (m) => { let c = 0; while (m) { m &= m - 1; c++; } return c; };
  const digitsOf = (m) => { const r = []; for (let d = 1; d <= 9; d++) if (m & bit(d)) r.push(d); return r; };

  const ROW = (i) => (i / 9) | 0, COL = (i) => i % 9, BOX = (i) => ((ROW(i) / 3) | 0) * 3 + ((COL(i) / 3) | 0);
  const UNITS = [];
  for (let r = 0; r < 9; r++) UNITS.push({ type: 'row', n: r, cells: [...Array(9)].map((_, c) => r * 9 + c) });
  for (let c = 0; c < 9; c++) UNITS.push({ type: 'col', n: c, cells: [...Array(9)].map((_, r) => r * 9 + c) });
  for (let b = 0; b < 9; b++) {
    const cells = [];
    for (let i = 0; i < 81; i++) if (BOX(i) === b) cells.push(i);
    UNITS.push({ type: 'box', n: b, cells });
  }
  const PEERS = [...Array(81)].map((_, i) => {
    const s = new Set();
    UNITS.forEach((u) => { if (u.cells.includes(i)) u.cells.forEach((c) => c !== i && s.add(c)); });
    return [...s];
  });

  function candidates(grid) {
    const cand = new Array(81).fill(0);
    for (let i = 0; i < 81; i++) {
      if (grid[i]) continue;
      let m = ALL;
      for (const p of PEERS[i]) if (grid[p]) m &= ~bit(grid[p]);
      cand[i] = m;
    }
    return cand;
  }

  /* Anzahl Lösungen (max. limit) per Backtracking mit MRV */
  function countSolutions(grid, limit = 2, wantSolution = false) {
    const g = grid.slice();
    let count = 0, sol = null;
    const cand = candidates(g);
    function rec() {
      if (count >= limit) return;
      let best = -1, bm = 10;
      for (let i = 0; i < 81; i++) {
        if (g[i]) continue;
        const n = pop(cand[i]);
        if (n === 0) return;
        if (n < bm) { bm = n; best = i; if (n === 1) break; }
      }
      if (best < 0) { count++; if (wantSolution && !sol) sol = g.slice(); return; }
      const m = cand[best];
      for (let d = 1; d <= 9; d++) {
        if (!(m & bit(d))) continue;
        g[best] = d;
        const saved = [];
        for (const p of PEERS[best]) if (!g[p] && (cand[p] & bit(d))) { saved.push(p); cand[p] &= ~bit(d); }
        const sm = cand[best]; cand[best] = 0;
        rec();
        cand[best] = sm;
        for (const p of saved) cand[p] |= bit(d);
        g[best] = 0;
        if (count >= limit) return;
      }
    }
    rec();
    return wantSolution ? { count, solution: sol } : count;
  }

  /* Logischer Löser. Techniken: 1 = Naked Single, 2 = Hidden Single, 3 = Pointing/Pair, 4 = Raten nötig */
  function nextStep(grid, cand, maxTech = 3) {
    // 1: Naked single
    for (let i = 0; i < 81; i++) if (!grid[i] && pop(cand[i]) === 1)
      return { tech: 1, kind: 'naked', cell: i, digit: digitsOf(cand[i])[0] };
    // 2: Hidden single
    if (maxTech >= 2) for (const u of UNITS) for (let d = 1; d <= 9; d++) {
      const spots = u.cells.filter((c) => !grid[c] && (cand[c] & bit(d)));
      if (spots.length === 1) return { tech: 2, kind: 'hidden', cell: spots[0], digit: d, unit: u };
    }
    if (maxTech >= 3) {
      // Pointing / Claiming
      for (const box of UNITS.filter((u) => u.type === 'box')) for (let d = 1; d <= 9; d++) {
        const spots = box.cells.filter((c) => !grid[c] && (cand[c] & bit(d)));
        if (spots.length < 2) continue;
        for (const type of ['row', 'col']) {
          const f = type === 'row' ? ROW : COL;
          if (spots.every((c) => f(c) === f(spots[0]))) {
            const line = UNITS.find((u) => u.type === type && u.n === f(spots[0]));
            const elim = line.cells.filter((c) => !box.cells.includes(c) && !grid[c] && (cand[c] & bit(d)));
            if (elim.length) return { tech: 3, kind: 'pointing', digit: d, elim: elim.map((c) => [c, d]) };
          }
        }
      }
      for (const line of UNITS.filter((u) => u.type !== 'box')) for (let d = 1; d <= 9; d++) {
        const spots = line.cells.filter((c) => !grid[c] && (cand[c] & bit(d)));
        if (spots.length < 2) continue;
        if (spots.every((c) => BOX(c) === BOX(spots[0]))) {
          const box = UNITS.find((u) => u.type === 'box' && u.n === BOX(spots[0]));
          const elim = box.cells.filter((c) => !line.cells.includes(c) && !grid[c] && (cand[c] & bit(d)));
          if (elim.length) return { tech: 3, kind: 'claiming', digit: d, elim: elim.map((c) => [c, d]) };
        }
      }
      // Naked Pair
      for (const u of UNITS) {
        const two = u.cells.filter((c) => !grid[c] && pop(cand[c]) === 2);
        for (let a = 0; a < two.length; a++) for (let b = a + 1; b < two.length; b++) {
          if (cand[two[a]] !== cand[two[b]]) continue;
          const m = cand[two[a]], elim = [];
          for (const c of u.cells) if (c !== two[a] && c !== two[b] && !grid[c] && (cand[c] & m))
            digitsOf(cand[c] & m).forEach((d) => elim.push([c, d]));
          if (elim.length) return { tech: 3, kind: 'pair', elim };
        }
      }
    }
    return null;
  }

  function applyStep(grid, cand, step) {
    if (step.cell !== undefined) {
      const { cell, digit } = step;
      grid[cell] = digit; cand[cell] = 0;
      for (const p of PEERS[cell]) cand[p] &= ~bit(digit);
    } else for (const [c, d] of step.elim) cand[c] &= ~bit(d);
  }

  /* Bewertet ein Rätsel: gibt höchste benötigte Technik zurück (4 = nicht rein logisch lösbar) */
  function rate(puzzle) {
    const g = puzzle.slice(), cand = candidates(g);
    let max = 1;
    for (;;) {
      if (g.every((v) => v)) return max;
      const s = nextStep(g, cand);
      if (!s) return 4;
      max = Math.max(max, s.tech);
      applyStep(g, cand, s);
    }
  }

  function shuffle(a) {
    for (let i = a.length - 1; i > 0; i--) { const j = (Math.random() * (i + 1)) | 0; [a[i], a[j]] = [a[j], a[i]]; }
    return a;
  }

  function randomSolution() {
    const g = new Array(81).fill(0);
    const cand = candidates(g);
    function rec() {
      let best = -1, bm = 10;
      for (let i = 0; i < 81; i++) if (!g[i]) { const n = pop(cand[i]); if (n < bm) { bm = n; best = i; } }
      if (best < 0) return true;
      for (const d of shuffle(digitsOf(cand[best]))) {
        g[best] = d;
        const saved = [];
        for (const p of PEERS[best]) if (!g[p] && (cand[p] & bit(d))) { saved.push(p); cand[p] &= ~bit(d); }
        const sm = cand[best]; cand[best] = 0;
        if (rec()) return true;
        cand[best] = sm;
        for (const p of saved) cand[p] |= bit(d);
        g[best] = 0;
      }
      return false;
    }
    rec();
    return g;
  }

  const LEVELS = [
    { id: 'anfaenger', name: 'Anfänger', target: 44, tech: 1, exact: true },
    { id: 'leicht', name: 'Leicht', target: 38, tech: 2, exact: false },
    { id: 'mittel', name: 'Mittel', target: 32, tech: 2, exact: true },
    { id: 'schwer', name: 'Schwer', target: 28, tech: 3, exact: true },
    { id: 'experte', name: 'Experte', target: 22, tech: 4, exact: true },
  ];

  function generate(levelId, maxAttempts = 60) {
    const L = LEVELS.find((l) => l.id === levelId) || LEVELS[1];
    let fallback = null;
    for (let attempt = 0; attempt < maxAttempts; attempt++) {
      const solution = randomSolution();
      const puzzle = solution.slice();
      let clues = 81;
      for (const i of shuffle([...Array(81).keys()])) {
        if (clues <= L.target) break;
        const v = puzzle[i];
        puzzle[i] = 0;
        // Technik-Limit: Level < Experte darf nie über seine Technik hinaus gehen
        if (countSolutions(puzzle, 2) !== 1 || (L.tech < 4 && rate(puzzle) > L.tech)) puzzle[i] = v; else clues--;
      }
      const t = rate(puzzle);
      const ok = L.exact ? t === L.tech : t <= L.tech;
      if (ok) return { puzzle, solution, level: L.id, clues };
      if (!fallback || (L.tech === 4 ? t > fallback.t : t >= fallback.t)) fallback = { puzzle, solution, level: L.id, clues, t };
    }
    return fallback;
  }

  /* Erklärt den nächsten sinnvollen Schritt (nutzt echte Kandidaten, nicht die Notizen) */
  const UNIT_DE = { row: 'Zeile', col: 'Spalte', box: 'Block' };
  function hint(vals, solution) {
    // Falsche Zahlen zuerst melden
    for (let i = 0; i < 81; i++) if (vals[i] && vals[i] !== solution[i])
      return { cell: i, digit: 0, wrong: true, text: 'Diese Zahl ist falsch – sie widerspricht der Lösung.' };
    const cand = candidates(vals);
    const s = nextStep(vals, cand, 2);
    if (s && s.kind === 'naked')
      return { cell: s.cell, digit: s.digit, text: `Nackter Single: In diesem Feld passt nur noch die ${s.digit}.` };
    if (s && s.kind === 'hidden')
      return { cell: s.cell, digit: s.digit, text: `Versteckter Single: Die ${s.digit} kann in dieser ${UNIT_DE[s.unit.type]} nur in diesem Feld stehen.` };
    // Kein einfacher Schritt: zeige ein Feld mit wenigsten Kandidaten
    let best = -1, bn = 10;
    for (let i = 0; i < 81; i++) if (!vals[i] && pop(cand[i]) < bn) { bn = pop(cand[i]); best = i; }
    if (best < 0) return null;
    return { cell: best, digit: solution[best], text: `Kein einfacher Schritt gefunden. Hier gehört die ${solution[best]} hin (Lösung).` };
  }

  const api = { LEVELS, generate, rate, countSolutions, candidates, hint, PEERS, UNITS, ROW, COL, BOX, bit, digitsOf, pop };
  if (typeof module !== 'undefined') module.exports = api; else root.SudokuEngine = api;
})(typeof self !== 'undefined' ? self : this);
