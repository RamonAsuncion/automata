# References:
# 1. https://www.youtube.com/watch?v=NhWDVqR4tZc
# 2. https://www.youtube.com/watch?v=32bC33nJR3A
# 2. https://en.wikipedia.org/wiki/Nondeterministic_finite_automaton
# 3. https://en.wikipedia.org/wiki/Deterministic_finite_automaton

def run_tests(automata, label, test_cases):
  sep="="*(len(label)+14)

  print(sep)
  print(f"Testing {label}")
  print(sep)

  print(automata)
  print()

  for test, expected in test_cases:
    result = automata.run(test)
    if result == expected:
      print(f"PASSED:\n\t Input: {test}\n\t Accepted: {result}\n")
    else:
      print(f"FAILED:\n\t Input: {test}\n\t Accepted: {result}\n")

  print(sep)

# use graphviz to visualize (do a bit of parsing)
def visualize():
  pass

class DFA:
  def __init__(self, Q, Σ, δ, q0, F):
    self.Q  = Q   # finite set of states
    self.Σ  = Σ   # finite set of input symbols (alphabet)
    self.δ  = δ   # transition function QxΣ->Q
    self.q0 = q0  # start state
    self.F  = F   # set of accept states
  
  def run(self, w): 
    q = self.q0
    while w != "":
      q = self.δ[(q,w[0])]
      w = w[1:]
    return q in self.F

  def toNFA(self):
    δ = {s: set(t) for s, t in self.δ.items()}
    return NFA(self.Q, self.Σ, δ, {self.q0}, self.F)

  def __repr__(self):
    return f"DFA({self.Q}),\n\t{self.Σ},\n\t{self.δ},\n\t{self.q0}\n\t{self.F}"

# L = { words where as come before bs } 
D0 = DFA({0,1,2},{"a","b"}, 
         {(0,"a"):0,(0,"b"):1,
          (1,"a"):2,(1,"b"):1,
          (2,"a"):2,(2,"b"):2},
          0,
          {0,1})

D0_tests = [
  # string, expected
  ("aabb", True),
  ("bba", False),
  ("aba", False)
]

run_tests(D0, "DFA0", D0_tests)

# L = { set of all string {0,1} that ends with 11}}
D1 = DFA({0,1,2},{0,1},
         {(0,"0"):0,(0,"1"):1,
         (1,"0"):0,(1,"1"):2,
         (2,"1"):2,(2,"0"):0},
         0,
         {2})

D1_tests = [
  ("0011", True),
  ("11", True),
  ("010111", True),
  ("1111", True),
  ("00", False),
  ("110", False)
]

run_tests(D1, "DFA1", D1_tests)

class NFA:
  def __init__(self, Q, Σ, δ, S, F):
    self.Q = Q  # finite set of states
    self.Σ = Σ  # finite set of input symbols (alphabet)
    self.δ = δ  # transition function QxΣ->P(Q)
    self.S = S  # set of start states
    self.F = F  # set of accept states

  def ε_closure(self,S):
    """ compute the eplison cloure of a set of state 
  
    the epsilon clsoure of a state is the set of states that can
    be reached from that state using only ε-transitions.

    reference: https://www.site.uottawa.ca/~bochmann/SEG-2106-2506/Notes/M2-2-LexicalAnalysis/Aho-algorithm3.2.pdf
    """
    C=set(S)      # closures
    stack=list(S) # explore epsilon transitions
    while stack:
      q=stack.pop()
      for new_q in self.δ.get((q,""),set()): # transition on empty 
        if new_q not in C:
          C.add(new_q)
          stack.append(new_q)
    return C

  def transition(self, q, x):
    return self.δ.get((q,x),set())

  def run(self, w):
    P = self.ε_closure(self.S)
    # P = self.S
    while w != "":
      new_P = set() # set of states after transition
      for q in P:
        new_P=new_P.union(self.transition(q,w[0]))
      P = self.ε_closure(new_P) # find epsilon closure for new states
      # P = new_P
      w = w[1:]
    return not P.isdisjoint(self.F) # intersection

  def toDFA(self):
    pass
        

  def __repr__(self):
    return f"NFA({self.Q}),\n\t{self.Σ},\n\t{self.δ},\n\t{self.S}\n\t{self.F}"

# L = { the penultimate (second to last) symbol is 1}
N0 = NFA({0,1,2},{0,1},
         {(0,"0"):{0},
          (0,"1"):{0,1},
          (1,"0"):{2}, 
          (1,"1"):{2}},
          {0},
          {2})

N0_tests = [
  # string, expected
  ("10", True),
  ("11", True),
  ("100", False),
  ("111", True),
]

run_tests(N0, "NFA0", N0_tests)

# reference: https://algos.world/21sp/notes/epsilon-closure.pdf
N1 = NFA({0,1,2,3,4},{0,1},
         {(0,"0"):{0},(0,""):{1},
          (1,"1"):{1},(1,""):{2},
          (2,"0"):{0},(2,""):{3},(2,"0"):{4}},
          {0},
          {3,4})

N1_tests = [
  # string, expected
  ("", True),
  ("0", True),
  ("1", True),
  ("010", True)
]

run_tests(N1, "NFA1", N1_tests)
