import sys

def abs(x):
	if x < 0:
		return -x
	else:
		return x

class term(list):
	def __init__(self, p=[]):
		l = list(set(p)) # Since we are over F_2 the term x^2 and x are the same.
		l.sort()
		super().__init__(l)

	def add(self, x):
		if not x in self:
			self.append(x)
			self = self.sort()

	def str(self):
		if self == []:
			return "1"
		else:
			return " ".join(["x"+str(v) for v in self])
	def remove(self, x):
		t = []
		for v in self:
			if v != x:
				t.append(v)
		return(t)
	
class polynomial(list):
	def __init__(self, l=[]):
		#removes an even number of copies of every repeated term, because we are over F_2
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
		super().__init__(l)

	def __contains__(self, x):
		return any(x in t for t in self)

	def str(self):
		return " + ".join([term(t).str() for t in self])

	def addition(self, p):
		return polynomial(self + p)

	def product(self, p):
		return polynomial([term(x+y) for x in self for y in p])


class clause(list):
	def __init__(self, p=[]):
		s = set()
		l = []
		for x in p:
			if x not in s:
				l.append(x)
				s.add(x)
		l.sort()
		super().__init__(l)

	def __add__(self,x):
		return clause(list(self) + list(x))

	def __sub__(self,c):
		return clause([x for x in self if x not in c])

	def str(self):
		return " ".join([str(x) for x in self])

	def tautology(self):
		s = set(self)
		return any(x for x in self if -x in s)

	def add(self, x):
		if not x in self:
			self.append(x)
			self = self.sort()

	def polynomial(self):
		p = polynomial([[]])
		for v in self:
			if v > 0:
				p=p.product(polynomial([[v],[]]))
			else:
				p=p.product(polynomial([[-v]]))
		return p

class formula:
	def __init__(self):
		self.numvar = 0
		self.clauses = []

	def parse(self, filename):
		with open(filename, "r") as file:
			lines = file.readlines()
			for l in lines:
				c = clause()
				for tok in l.split():
					if tok == "c" or tok == "p":
						break
					if tok == "0":
						self.add(c)
						c = clause()
					else:
						x = int(tok)
						if abs(x) > self.numvar:
							self.numvar = abs(x)
						c.add(x)

	def add(self, c):
		if not c.tautology():
			self.clauses.append(c)


if __name__ == '__main__':
	if len(sys.argv) < 2:
		print("Usage: python cnf2pol.py file.cnf")
		sys.exit(1)

	f = formula()
	f.parse(sys.argv[1])
	for c in f.clauses:
		print(c.polynomial().str())


