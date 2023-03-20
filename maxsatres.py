import sys, getopt
from random import random

def abs(x):
	if x < 0:
		return -x
	else:
		return x

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

	def __str__(self):
		if self == []:
			return '0'
		return ' '.join([str(x) for x in self])

	def width(self):
		return len(self)

	def key(self):
		return tuple(self)

	def tautology(self):
		s = set(self)
		return any(x for x in self if -x in s)

	def occurs(self,x):
		return any(x==v for v in self) or any(-x==v for v in self)

	def add(self, x):
		if not x in self:
			self.append(x)
			self = self.sort()

	def intersection(self, c):   #returns a "list" of literals "v" in self such that -v is in c
		return [v for v in self if -v in c]

class formula:
	def __init__(self):
		self.numvar = 0
		self.clauses = []
		self.rem = set()   #indicates if a clause index has been removed

	def __str__(self, sel = {}):
		return "\n".join([str(i)+":  "+str(c)+"\tReason: "+str(r) for i, (c, r) in enumerate(self.clauses) if sel == {} or i in sel])

	def minimal(self):
		#returns the cost and the minimal set of clauses needed at the proof
		needed = []
		for i, (c, r) in enumerate(self.clauses):
			if c == []:
				needed.append(i)
		cost = len(needed)
		for i in needed:
			for j in self.clauses[i][1]:
				if j not in needed:
					needed.append(j)
		return cost, set(needed)
				
	def parse(self, filename):
		with open(filename, "r") as file:
			lines = file.readlines()
			for l in lines:
				c = clause()
				for tok in l.split():
					if tok == "c" or tok == "p":
						break
					if tok == "0":
						self.add(c, [])
						c = clause()
					else:
						x = int(tok)
						if abs(x) > self.numvar:
							self.numvar = abs(x)
						c.add(x)

	def add(self, c, r):
		if not c.tautology():
			self.clauses.append((c, r))
			if verbose > 1:
				print("ADDED (",len(self.clauses)-1,"): ", c)

	def satura(self,x):
		finish = False
		while not finish:
			finish = True
			lcx  = [i for i in range(len(self.clauses)) if i not in self.rem and  x in self.clauses[i][0]]
			lcnx = [i for i in range(len(self.clauses)) if i not in self.rem and -x in self.clauses[i][0]]
			if randomize:
				lcx.sort(key = lambda x : (self.clauses[x][0].width()+random()))
				lcnx.sort(key = lambda x : (self.clauses[x][0].width()+random()))
			else:
				lcx.sort(key = lambda x : (self.clauses[x][0].width()))
				lcnx.sort(key = lambda x : (self.clauses[x][0].width()))

			if verbose > 0:
				print("WIDTHS: ",list(map(lambda x : (self.clauses[x][0].width()), lcx)), list(map(lambda x : (self.clauses[x][0].width()), lcnx)))

			for i in lcx:
				for j in lcnx:
					if i in self.rem or j in self.rem:
						continue
					c1 = self.clauses[i][0]
					c2 = self.clauses[j][0]
					c = c1.intersection(c2)
					if len(c) > 1: 
						continue # A tautology would be generated
					if verbose > 1:
						print("\n---CUT of (",i,") and (", j,")---")
					a = c1 - clause([x])
					b = c2 - clause([-x])
					self.add(a + b, [i,j])
					for k in range(0, len(b)):
						self.add(c1 + b[0:k] + [-b[k]], [i,j])	
					for k in range(0, len(a)):
						self.add(c2 + a[0:k] + [-a[k]], [i,j])	
					self.rem.add(i)
					self.rem.add(j)
					finish = False
					break
		if verbose > 0:
			print("\n---SATURATED for ",x,"---")
		for i,(c,_) in enumerate(self.clauses):				
			if x in c or -x in c:
				self.rem.add(i)

verbose = 0
randomize = False

if __name__ == '__main__':
	opts, args = getopt.getopt(sys.argv[1:], "hv:r")
	for opt, arg in opts:
		if opt == '-h':
			print("Usage: python maxsatres.py [-h] [-v <verblevel>] [-r] file.cnf\n -h : this help\n -v <verblevel>: verbose level in [0,1,2]\n -r : randomize the order of clauses\n -g : generates graph of the proof", arg)
			sys.exit(0)
		if opt == '-v':
			verbose = int(arg)
		if opt == "-r":
			randomize = True
				
	if len(args) < 1:
		print("Usage: python maxsatres.py file.cnf")
		sys.exit(1)

	f = formula()
	f.parse(args[0])
	for x in range(1, f.numvar+1):
		f.satura(x)

	cost, m = f.minimal()
	size = len(set([f.clauses[i][0].key() for i in m]))

	if verbose > 0:
		print('---PROOF---')
		print(f.__str__(m))
	print('COST:', cost, 'SIZE:', size)




