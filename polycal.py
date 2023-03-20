import sys, getopt
from random import shuffle, random
from time import process_time
import networkx
import matplotlib.pyplot as plt


def reverse(mydict, i): # search in a dictionary by value, return key
	    return list(mydict.keys())[list(mydict.values()).index(i)]

name = {} #Assignas a name (string) to each variable (number)

class term(list):
	def __init__(self, p=[]):
		l = list(set(p)) # Since we are over F_2 the term x^2 and x are the same.
		l.sort()
		super().__init__(l)

	def __str__(self):
		if self == []:
			return "1"
		else:
			return " ".join([reverse(name,v) for v in self])

	def add(self, x):
		if not x in self:
			self.append(x)
			self = self.sort()

	def remove(self, x):
		t = []
		for v in self:
			if v != x:
				t.append(v)
		return(t)
	
class polynomial(list):
	def __init__(self, l=[]):
		#removes an even number of copies of every repeated term, because we are over F_2
		#print("ENTRY:", l)
		seen = set()
		dupes = []
		for x in l:
			if tuple(x) in seen:
				dupes.append(x)
				seen.remove(tuple(x))
			else:
				seen.add(tuple(x))
		for d in dupes:
			l.remove(d)
			l.remove(d)
		l.sort()
		#print("EXIT:", l)
		super().__init__(l)

	def __contains__(self, x):
		return any(x in t for t in self)

	def __str__(self):
		return " + ".join([term(t).__str__() for t in self])

	def factor(self, x):
		#Returns p and q such that self = p * x + q
		p = polynomial()
		q = polynomial()
		for t in self:
			if x in t:
				p.append(t.remove(x))
			else:
				q.append(t)
		return (p, q)

	def __add__(self, p):
		return polynomial(list(self) + list(p))

	def __mul__(self, p):
		return polynomial([term(x+y) for x in self for y in p])

	def degree(self):
		return max([len(t) for t in self])

	def tautology(self):
		return len(self) == 0

	def key(self):
		return tuple([tuple(t) for t in self])

one = polynomial([term([])])

class clause:
	def __init__(self, p, w=1, r=[]):
		self.poly = p
		self.weight = w
		self.reason = r

class formula:
	def __init__(self):
		self.idv = 0
		self.idc = 0
		self.clauses = []
		self.seen = {}

	def __str__(self, needed = {}):
		return "\n".join([str(i)+":  "+str(c.poly)+"\tReason: "+str(c.reason) for i, c in enumerate(self.clauses) if needed == {} or i in needed])

	def newvar(self):
		self.idv += 1
		return(self.idv)

	def minimal(self):
		# Returns the cost and the minimal set of polynomials needed at the proof
		needed = []
		cost = 0
		for i, c in enumerate(self.clauses):
			if c.poly == one:
				needed.append(i)
				cost += c.weight
		for i in needed:
			for j in self.clauses[i].reason:
				if j not in needed:
					needed.append(j)
		return cost, set(needed)

	def minimalGraph(self):
		# Constructs a minimal proof graph
		g = networkx.DiGraph()
		seennode = []
		seenedge = []
		_, needed = self.minimal()
		next = 0
		for i in needed:
			k = self.clauses[i].poly.key()
			if k not in seennode:
				if len(self.clauses[i].reason)==0:
					t = 'axiom'
				else:
					t = 'clause'
				g.add_node(len(seennode), label=str(len(seennode))+': '+str(self.clauses[i].poly), type=t)
				seennode.append(k)
		for i in needed:
			premises = [seennode.index(self.clauses[j].poly.key()) for j in self.clauses[i].reason]
			premises.sort()
			if len(premises) > 0: #if there are premises
				k = tuple(premises)
				if k not in seennode:
					g.add_node(len(seennode), label=str(premises), type='rule')
					seennode.append(k)
				r = seennode.index(k)
				for j in self.clauses[i].reason:
					c = seennode.index(self.clauses[j].poly.key())
					a = (c, r)
					if a not in seenedge:
						g.add_edge(c,r)
						seenedge.append(a)
				c = seennode.index(self.clauses[i].poly.key())
				a = (r, c)
				if a not in seenedge:
					g.add_edge(r,c)
					seenedge.append(a)
		return g

	def parse(self, filename=None):
		# Ilario: I think we should add a check to ignore empty lines
		with open(filename, "r") if filename != None else sys.stdin as file:
			lines = file.readlines()
			for l in lines:
				t = term()
				p = []
				for tok in l.split():
					if tok == "+":
						p.append(t)
						t = term()
					else:
						if tok != "1":
							if tok not in name:
								name[tok] = self.newvar()
							t.add(name[tok])
				p.append(t)
				self.add(polynomial(p), 1, []) # Add polynomial with weight one

	def add(self, p, w=1, r=[]):
		if verbose > 2 and p.tautology():
			raise Exception('Trying to add a tautology to the formula')
		k = p.key()
		if k in self.seen:   # The clause already exists
			aux = self.seen[k]
			self.clauses[aux].weight += w
			self.clauses[aux].reason += r
			if verbose > 1:
				print(f"INCREMENTED WEIGHT ({aux}, {self.clauses[aux].weight}): {p}")
			return aux
		else:
			aux = len(self.clauses)
			if verbose > 1:
				print(f"ADDED ({aux},{w}): {p}")
			self.clauses.append(clause(p, w, r))
			self.seen[p.key()] = aux
			return aux

	def applysum(self, i, j):
		# Apply the inference SUM to clauses i and j
		if verbose > 2 and (self.clauses[i].weight == 0 or self.clauses[j].weight == 0):
			raise Exception(f"Clause {i} or {j} does not exist")
		m = min(self.clauses[i].weight, self.clauses[j].weight)
		if verbose > 1:
			print(f"\n---SUM of ({i}) and ({j})---")
		if verbose > 2 and (self.clauses[i].poly + self.clauses[j].poly).tautology():
			raise Exception(f'Sum of {i} and {j} results into tautology')
		aux = self.add(self.clauses[i].poly + self.clauses[j].poly, m, [i,j])
		p = self.clauses[i].poly * self.clauses[j].poly
		if not p.tautology():
			self.add(p, 2*m, [i,j])
		self.clauses[i].weight -= m
		self.clauses[j].weight -= m
		return aux

	def applysplit(self, i, p):
		# Apply the inference SPLIT to clause i and polynomial p
		if verbose > 2 and self.clauses[i].weight == 0:
			raise Exception(f"Clause {i} does not exist")
		if p == one or p.tautology():
			raise Exception(f"WARNING split ({i}) with p={p}")
			return i
		if verbose > 1:
			print(f"\n---SPLIT of ({i}) by {p}---")
		aux = self.add(self.clauses[i].poly * p, self.clauses[i].weight, [i])
		self.add(self.clauses[i].poly * (p + one), self.clauses[i].weight, [i])
		self.clauses[i].weight = 0
		return aux

	def satura(self,x):
		finish = False

		p = {}
		q = {}
		while not finish:
			finish = True
			lc = [i for i in range(len(self.clauses)) if self.clauses[i].weight > 0 and x in self.clauses[i].poly]
			if randomize:
				lc.sort(key = lambda x : (self.clauses[x].poly.degree()+random()))
			else:
				lc.sort(key = lambda x : (self.clauses[x].poly.degree()+0.0001*len(self.clauses[x].poly)))

			if verbose > 0:
				print("DEGREES: ",list(map(lambda x : (self.clauses[x].poly.degree()), lc)))

			if strategy:
				for i in lc:
					for j in lc:
						if i<j and (self.clauses[i].poly * self.clauses[j].poly).tautology():
							self.applysum(i, j)
							finish = False
							lc.remove(i)
							lc.remove(j)
							break #since cj is removed, break the loop
			if strategy and not finish:
				continue  #Never enter in the following if strategy can be applied

			for i in lc:
				ci = self.clauses[i].poly
				for j in lc:
					cj = self.clauses[j].poly
					if not i in p:
						(p[i], q[i]) = ci.factor(x)
					if not j in p:
						(p[j], q[j]) = cj.factor(x)
					if not ((q[i] + q[j])*(p[i] + p[j] + one)).tautology():
						aux = self.applysum(i,j)
						if x in self.clauses[aux].poly:
							(p[aux], q[aux]) = self.clauses[aux].poly.factor(x)
							if  not (q[aux] * (p[aux] + one)).tautology():
								self.applysplit(aux, p[aux])
						finish = False
						lc.remove(i)
						lc.remove(j)
						break #since ci is removed, break the loop
			for i in lc:
				ci = self.clauses[i].poly
				if not i in p:
					(p[i], q[i]) = ci.factor(x)
				if not (q[i] * (p[i] + one)).tautology():
					self.applysplit(i, p[i])
					finish = False
					lc.remove(i)
					break

		if verbose > 0:
			print("\n---SATURATED for ",reverse(name, x),"---")
		for i,c in enumerate(self.clauses):
			if x in c.poly:
				self.clauses[i].weight = 0

verbose = 0
randomize = False
printgraph = False
strategy = False

if __name__ == '__main__':
	opts, args = getopt.getopt(sys.argv[1:], "hv:rgs")
	for opt, arg in opts:
		if opt == '-h':
			print("Usage: python polycal.py [-h] [-v <verblevel>] [-r] [-g] [-s] [file.pol]\n -h : this help\n -v <verblevel>: verbose with level in [0,1,2,3]\n -r : randomize the order of clauses\n -g : generates graph of the proof\n -s : uses the strategy of searching for pairs of clauses where p * q = 0", arg)
			sys.exit(0)
		if opt == '-v':
			verbose = int(arg)
		if opt == "-r":
			randomize = True
		if opt == "-g":
			printgraph = True
		if opt == "-s":
			strategy = True
				
	f = formula()
	if len(args) == 1:
		f.parse(args[0])
	else:
		f.parse()

	t0 = process_time()
	for x in range(1,f.idv+1):
		f.satura(x)
	t1 = process_time()

	cost, m = f.minimal()
	size = len(set([c.poly.key() for c in f.clauses]))
	if verbose > 0:
		print('---PROOF---')
		print(f)
	print(f'{cost}\t{size}\t{t1-t0}')

	if printgraph:
		g = f.minimalGraph()
		pos = networkx.spring_layout(g)
		networkx.draw(g, pos)

		labels = networkx.get_node_attributes(g, "label")
		types = networkx.get_node_attributes(g, "type")
	
		networkx.draw_networkx_nodes(g, pos, nodelist=[i for i in types.keys() if types[i]=='rule'], node_color="tab:red")
		networkx.draw_networkx_nodes(g, pos, nodelist=[i for i in types.keys() if types[i]=='axiom'], node_color="tab:green")
		networkx.draw_networkx_labels(g, pos, labels=labels, font_size=7)

		plt.show()



