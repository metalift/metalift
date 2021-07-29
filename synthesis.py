import subprocess
import pyparsing as pp
import os

from ir import Expr


def flatten(L):
	for l in L:
		if isinstance(l,list):
			yield "("
			yield from flatten(l)
			yield ")"
		else:
			yield l

def generateAST(expr):
	s_expr = pp.nestedExpr(opener='(', closer=')')
	parser = pp.ZeroOrMore(pp.Suppress('(exit)') | s_expr)
	ast = parser.parseString(expr, parseAll=True).asList()
	return ast

def extractFuns(funDef):
	funDecls = []
	ast = generateAST(funDef)
	for a in ast:
		if 'define-fun-rec' in a:
			funDecls.append('( ' + ' '.join(list(flatten(a))) + ' )')
	return funDecls

def extractSynth(funDef, preds):
	synthDecls = {}
	lines = funDef.split("\n")
	for p in preds:
		for l in lines:
			if p in l:
				synthDecls[p] = l.replace('synth-fun', 'define-fun')
	return synthDecls

def generateCand(synthDecls, line):
	candidates = []
	ast  = generateAST(line)
	for k in synthDecls.keys():
		for a in ast[0]:
			if k in a:
				candidates.append(synthDecls[k] + ' ('  + ' '.join(list(flatten(a[1]))) + '))')
	return candidates

def callCVC(funDef, vars, predDecls, vc, cvcPath, basename):
	synthDir = './synthesisLogs/'
	if not os.path.exists(synthDir):
		os.mkdir(synthDir)
	sygusFile = synthDir + basename + ".sl"

	# Generate sygus file for synthesis
	toSMT(funDef, vars, predDecls, vc, sygusFile, True)

	logfile = synthDir + basename + '_logs.txt'
	synthLogs = open(logfile,'a')
	#Run synthesis subprocess
	proc = subprocess.Popen([cvcPath, '--lang=sygus2', '--output=sygus' ,  sygusFile],stdout=synthLogs,stderr=subprocess.DEVNULL)
	
	preds = [p.args[0] for p in predDecls]
	funs = "\n".join(d for d in extractFuns(funDef))
	synthDecls = extractSynth(funDef, preds)
	logfileVerif = open(logfile,"r")
	while True:
		line = logfileVerif.readline()
		if 'sygus-candidate' in line:
			print("Current PS and INV Guess ", line)
			candidates = "\n".join(d for d in generateCand(synthDecls, line))
			smtFile = synthDir + basename + ".smt"
			toSMT(funs, vars, candidates, vc, smtFile, False)

			#run external verification subprocess
			procVerify = subprocess.Popen([cvcPath, '--lang=smt', '--fmf-fun', '--tlimit=10000' ,  smtFile],stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
			output = procVerify.stdout.readline()
			output = output.decode("utf-8")
			if output.count('unsat') == 1:
				print("UNSAT\n")
				print("Verified PS and INV Candidates ", candidates)
				break
			else:
				print("CVC4 verification Result for Current Guess")
				print("SAT\n")


def synthesize(invAndPs, vars, preds, vc, ansFile, cvcPath, basename):
	# grammars = [genGrammar(p) for p in invAndPs]
	grammars = open(ansFile, mode="r").read()

	callCVC(grammars, vars, preds, vc, cvcPath, basename)

# programmatically generated grammar
# def genGrammar (modifiedVars, inScopeVars):
#   f = Expr.Choose(Expr.Lit(1, Type.int()), Expr.Lit(2, Type.int()), Expr.Lit(3, Type.int()))
#   e = Expr.Choose(*filter(lambda v: v.type == Type.int(), inScopeVars))
#   d = Expr.And(Expr.Ge(e, f), Expr.Le(e, f))
#   c = Expr.Eq(e, Expr.Call("sum_n", Expr.Sub(e, f)))
#   return Expr.And(c, d)


# print to a file
def toSMT(invAndPs, vars, preds, vc, outFile, isSynthesis):
	# order of appearance: inv and ps grammars, vars, non inv and ps preds, vc
	with open(outFile, mode="w") as out:
		out.write("%s\n\n" % invAndPs)

		v = "\n".join(["(declare-const %s %s)" % (v.args[0], v.type) for v in vars])  # name and type
		out.write("%s\n\n" % v)


		if isinstance(preds, str):
			out.write("%s\n\n" % preds)

		# a list of Exprs - print name, args, return type
		elif isinstance(preds, list):
			preds = "\n".join(["(define-fun %s (%s) (%s) )" %
										    (p.args[0], " ".join("(%s %s)" % (a.args[0], a.type) for a in p.args[1:]), p.type)
										    for p in preds])
			out.write("%s\n\n" % preds)

		else: raise Exception("unknown type passed in for preds: %s" % preds)

		if isSynthesis:
			out.write("%s\n\n" % Expr.Constraint(vc))
			out.write("(check-synth)")
		else:
			out.write("%s\n\n" % Expr.Assert(Expr.Not(vc)))
			out.write("(check-sat)\n(get-model)")
