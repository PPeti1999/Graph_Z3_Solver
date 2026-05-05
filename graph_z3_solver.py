from z3 import *

# ============================================================
# Union-Find visszalépéssel (trail)
# ============================================================
class UFNode:
    # Csomópont az unió-kereséshez.
    # term: amihez tartozik; id: a term azonosítója;
    # root: kezdetben saját gyökér, 1 méretű
    def __init__(self, term):
        self.term = term
        self.id   = term.get_id()
        self.root = self
        self.size = 1

class UnionFind:
    # Unió-keres gép.
    # _nodes: id -> UFNode; trail: visszalépéshez napló
    def __init__(self, trail):
        self._nodes = {}
        self.trail  = trail

    # Csomópont lekérése/létrehozása egy term-hez (undo-val).
    def get_node(self, a):
        aid = a.get_id()
        if aid in self._nodes:
            return self._nodes[aid]
        n = UFNode(a)
        self._nodes[aid] = n
        def undo():
            del self._nodes[aid]
        self.trail.append(undo)
        return n

    # Gyökér megkeresése rooton
    def find(self, a_node):
        root = a_node
        while root != root.root:
            root = root.root
        return root

    # Unió: két komponens egyesítése (kisebbet a nagyobb alá), undo-val.
    def union(self, a, b):
        ar = self.find(self.get_node(a))
        br = self.find(self.get_node(b))
        if ar == br:
            return
        if ar.size < br.size:
            ar, br = br, ar
        old_br_root, old_ar_size = br.root, ar.size
        br.root, ar.size = ar, ar.size + br.size
        def undo():
            br.root, ar.size = old_br_root, old_ar_size
        self.trail.append(undo)

# ============================================================
# AcyclicPropagator: erdő (körmentes) gráf T-propagálással
# ============================================================
class AcyclicPropagator(UserPropagateBase):
    """
    Cél: körmentes (erdő) gráf.
    - Ha egy új él (u,v) ugyanabba a komponensbe esik: azonnal conflict (kör).
    - Ha két komponens összeér: a komponensen belüli összes (x,y) párra tiltást tolok: ¬edge(x,y).
      (A faéleket nem tiltom, azok kellenek a fához.)
    'eager=False' esetén a tiltópropagálást nem hívom meg azonnal, így nagyobb eséllyel látsz
    explicit ciklus-konfliktust és visszalépést.
    """
    def __init__(self, s, edge_func, nodes, verbose=True, eager=False):
        super().__init__(s)
        self.nodes   = nodes
        self.n       = len(nodes)
        self.edge    = edge_func
        self.verbose = verbose
        self.eager   = eager

        self.trail = []         # ide írom fel, mit kell visszacsinálni visszalépéskor
        self.lim   = []         # stack-határok a trail-hez
        self.uf    = UnionFind(self.trail)  # komponenseket ezzel tartom egyben

        self.fixed_edges       = []   # itt gyűjtöm a már igazra állt faéleket
        self._true_edge_keys   = set()# gyors szűrés: (min_id,max_id) kulcs a faélekhez
        self._propagated_pairs = set()# mire toltam már ki tiltást (¬edge), hogy ne duplázzak

        # Callbackek
        self.add_fixed(self._fixed)   # ha egy literál fixálódik (igaz/hamis)
        self.add_eq(self._eq)
        self.add_created(self._created)
        self.add_final(self._final)

        # Minden csúcs regisztrálása UF-ben
        for v in self.nodes:
            self.uf.get_node(v)

        # Előre regisztrálom az edge(i,j) literálokat csak i<j-re (irányfüggetlen modell)
        for i in range(self.n):
            for j in range(i + 1, self.n):
                lit = self.edge(self.nodes[i], self.nodes[j])
                if self.verbose:
                    print(f"Register {lit}")
                self.add(lit)

    # --- Solver stack ---
    def push(self):
        if self.verbose:
            print("PUSH")
        self.lim.append(len(self.trail))

    def pop(self, scopes):
        for _ in range(scopes):
            if self.verbose:
                print("POP")
            num_trail = self.lim.pop()
            while len(self.trail) > num_trail:
                self.trail.pop()()

    # --- Callbacks ---
    def _created(self, t):
        if t.decl().eq(self.edge):
            if self.verbose:
                print(f"Created {t}")
            self.add(t)

    def _eq(self, u, v):
        if self.verbose:
            print(f"Eq: {u} = {v}  -> UF.union")
        self.uf.union(u, v)

    def _fixed(self, t, val):
        if not t.decl().eq(self.edge):
            return
        if self.verbose:
            print(f"fixed:  {t}  :=  {val}")

        if is_true(val):
            u, w = t.arg(0), t.arg(1)

            # Ha u és w már egy komponens: kör lenne -> conflict
            if self.uf.find(self.uf.get_node(u)) == self.uf.find(self.uf.get_node(w)):
                reason = self._path_edges_in_tree(u, w)
                if self.verbose:
                    if reason:
                        rtxt = ", ".join(str(r) for r in reason)
                        print(f"Conflict (cycle): adding {t} would close cycle; reason: [{rtxt}]")
                    else:
                        print(f"Conflict (cycle): adding {t} would close cycle")
                deps = [t] + reason if reason else [t]
                self.conflict(deps)
                return

            # Külön komponensek -> összeolvasztom és eltárolom a faélt
            if self.verbose:
                print(f"Union (tree edge): {u} ~ {w}")
            self.uf.union(u, w)
            self._push_fixed_edge(t)

            # T-propagate tiltások: eager módban azonnal, lazy módban kihagyjuk itt
            if self.eager:
                self._propagate_for_component(u)

        elif is_false(val):
            if self.verbose:
                print(f"info: {t} is fixed to False")

    def _final(self):
        print("final check (noop for forest).")

    # --- Helpers ---
    def _push_fixed_edge(self, edge_term):
        self.fixed_edges.append(edge_term)
        u, v = edge_term.arg(0), edge_term.arg(1)
        key = (min(u.get_id(), v.get_id()), max(u.get_id(), v.get_id()))
        self._true_edge_keys.add(key)
        if self.verbose:
            print(f"TreeEdge+: {edge_term}")
        def undo():
            if self.fixed_edges:
                last = self.fixed_edges.pop()
                uu, vv = last.arg(0), last.arg(1)
                k2 = (min(uu.get_id(), vv.get_id()), max(uu.get_id(), vv.get_id()))
                if k2 in self._true_edge_keys:
                    self._true_edge_keys.remove(k2)
                if self.verbose:
                    print(f"TreeEdge-: {last} (undo)")
        self.trail.append(undo)

    def _adjacency(self):
        """Aktuális fa-adjacencia a fixed_edges alapján (irány nélkül)."""
        adj = {i: set() for i in range(self.n)}
        id_to_idx = {self.nodes[i].get_id(): i for i in range(self.n)}

        def idx_of(a):
            return id_to_idx.get(a.get_id(), None)

        for e in self.fixed_edges:
            a, b = e.arg(0), e.arg(1)
            ia, ib = idx_of(a), idx_of(b)
            if ia is None or ib is None or ia == ib:
                continue
            adj[ia].add(ib)
            adj[ib].add(ia)
        return adj

    def _path_edges_in_tree(self, u, w):
        """Visszaad egy u–w faútat reprezentáló él-terminus listát (bizonyítékhoz)."""
        adj = self._adjacency()
        id_map = {self.nodes[i].get_id(): i for i in range(self.n)}
        su, sw = id_map.get(u.get_id(), None), id_map.get(w.get_id(), None)
        if su is None or sw is None:
            return []

        from collections import deque
        q = deque([su])
        parent = {su: None}
        while q:
            cur = q.popleft()
            if cur == sw:
                break
            for nb in adj[cur]:
                if nb not in parent:
                    parent[nb] = cur
                    q.append(nb)

        if sw not in parent:
            return []

        # visszafejtjük az út csúcsait
        path = []
        v = sw
        while v is not None:
            path.append(v)
            v = parent[v]
        path.reverse()

        # útból éltermek (irányfüggetlenül, mindig kisebb index -> nagyobb index)
        deps = []
        for i in range(len(path) - 1):
            a, b = path[i], path[i + 1]
            i0, i1 = (a, b) if a < b else (b, a)
            deps.append(self.edge(self.nodes[i0], self.nodes[i1]))
        return deps

    def _propagate_for_component(self, seed):
        """
        T-Propagate: a 'seed' komponensében minden (x,y) párra propagáljuk, hogy ¬edge(x,y),
        DE ha (x,y) jelenleg faél (true), akkor SKIP.
        """
        adj = self._adjacency()
        id_map = {self.nodes[i].get_id(): i for i in range(self.n)}
        sid = id_map[seed.get_id()]

        from collections import deque
        q = deque([sid])
        seen = {sid}
        comp = []
        while q:
            cur = q.popleft()
            comp.append(cur)
            for nb in adj[cur]:
                if nb not in seen:
                    seen.add(nb)
                    q.append(nb)

        # minden párra tiltsuk az élt: ¬edge(a,b), ha NEM faél
        for i in range(len(comp)):
            for j in range(i + 1, len(comp)):
                a_idx, b_idx = comp[i], comp[j]
                a, b = self.nodes[a_idx], self.nodes[b_idx]
                key = (min(a.get_id(), b.get_id()), max(a.get_id(), b.get_id()))

                if key in self._true_edge_keys:        # ne tiltsuk a faélt!
                    continue
                if key in self._propagated_pairs:       # idempotencia
                    continue

                reason = self._path_edges_in_tree(a, b)
                lit = self.edge(self.nodes[min(a_idx, b_idx)], self.nodes[max(a_idx, b_idx)])
                if self.verbose:
                    rtxt = ", ".join(str(r) for r in reason)
                    print(f"Propagate: ¬{lit}   reason: [{rtxt}]")
                self.propagate(Not(lit), reason)

                self._propagated_pairs.add(key)
                def undo(key_=key):
                    if key_ in self._propagated_pairs:
                        self._propagated_pairs.remove(key_)
                        if self.verbose:
                            print(f"Unpropagate mark removed for key={key_} (undo)")
                self.trail.append(undo)

    def true_edges(self):
        """Igaz élek (irányfüggetlen listában)."""
        undirected = {}
        for e in self.fixed_edges:
            u, v = e.arg(0), e.arg(1)
            key = (min(u.get_id(), v.get_id()), max(u.get_id(), v.get_id()))
            undirected[key] = (u, v)
        return list(undirected.values())


# ============================================================
# A PROGRAM FUTTATÁSA
# ============================================================
def make_edge_count_lower_bound_smt(n: int) -> str:
        # Minden i<j párra (ite (edge ni nj) 1 0), és ezek összege >= n-1
        pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
        terms = "\n           ".join([f"(ite (edge n{i} n{j}) 1 0)" for (i, j) in pairs])
        smt = f"""
    ; ===== {n} csúcs (n0..n{n-1}) =====
    ; Legalább n-1 él -> solver tipikusan fát választ (n-1 él), a propagátor megakadályozza a köröket.
    (assert
    (>=
        (+ {terms})
        {n - 1}))
    """
        return smt

if __name__ == "__main__":
 # n csúcsra általánosan
    n = 5  #  bármire átírhatod: 3,4,5,6,7...
    NodeSort = DeclareSort('Node')
    nodes = [Const(f'n{i}', NodeSort) for i in range(n)]
    edge_func = PropagateFunction('edge', NodeSort, NodeSort, BoolSort())

    decls_map = {f'n{i}': nodes[i] for i in range(n)}
    decls_map['edge'] = edge_func

    example_graph = make_edge_count_lower_bound_smt(n)  # csak az alsó korlát

    formulas = parse_smt2_string(example_graph, sorts={'Node': NodeSort}, decls=decls_map)

    print("Körmentes gráf keresése T-propagálással (erdő-logika)…")
    s = Solver()

    # Állítsd eager=False-ra, ha kifejezetten szeretnél 'Conflict (cycle)' logot és backtracket látni.
    prop = AcyclicPropagator(s, edge_func, nodes, verbose=True, eager=False)
    s.add(formulas)
    res = s.check()
    print("Eredmény:", res)

    if res == sat:
        print("\n" + "="*20 + " MEGOLDÁS " + "="*20)
        print("A modell egy körmentes gráf. Igaz élek (irány nélkül):")
        solution_edges = prop.true_edges()
        for (u, v) in solution_edges:
            print(f"  ({u}, {v})")
        print(f"Összesen {len(solution_edges)} él.")

        # Szomszédsági lista
        adj = {str(n): [] for n in nodes}
        for (u, v) in solution_edges:
            adj[str(u)].append(str(v))
            adj[str(v)].append(str(u))
        print("Adjacency:")
        for k in sorted(adj):
            print(" ", k, "->", sorted(adj[k]))
        
    else:
        print("Nem található megoldás (unsat).")
