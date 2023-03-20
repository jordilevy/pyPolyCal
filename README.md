# pyPolyCal
An implementation of the Polynomial Calculus for MaxSAT in Python

<h2>--- polycal.py ---</h2>

Construct a MaxSAT polynomial calculus proof for a set of polynomials in "pol" format.

Usage: python polycal.py [-h] [-v <verblevel>] [-r] [-g] [-s] [file.pol]<br/>
	-h : this help<br/>
	-v <verblevel>: verbose with level in [0,1,2,3]<br/>
	-r : randomize the order of clauses<br/>
	-g : generates graph of the proof<br/>
	-s : uses the strategy of searching for pairs of clauses where p * q = 0 

Example: python3 polycal.py -v 2 -r examples/clique7.pol

<h2>--- maxsatres.py ---</h2>

Constructs a MaxSATresolution proof for a formula in "cnf" DIMACS format.
(Notice that the format is "cnf", not "wcnf").

Usage: python maxsatres.py [-h] [-v <verblevel>] [-r] file.cnf<br/>
 -h : this help<br/> 
 -v <verblevel>: verbose level in [0,1,2]<br/>
 -r : randomize the order of clauses<br/>
 -g : generates graph of the proof<br/>
 
 Example: python3 maxsatres.py -v2 -r examples/clique7.cnf
 
 <h2>--- cnf2pol.py ---</h2>
 
Translates a formula from "cnf" format to "pol" format.

Usage: python cnf2pol.py file.cnf

Example: python3 cnf2pol.py examples/clique7.cnf >examples/clique7.pol
