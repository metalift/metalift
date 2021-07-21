import subprocess 
import io
import pyparsing as pp
import os

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

def runSynthesis(v, vcSygus, funDef, vc, predDecls, cvcPath, basename):
	vcSygus = vcSygus.replace("assert", "constraint")
	synthDir = './synthesisLogs/'
	if not os.path.exists(synthDir):
		os.mkdir(synthDir)
	sygusFile = synthDir + basename + ".sl"
	#Generate sygus file for synthesis
	with open(sygusFile, mode="w") as out:
		out.write("%s\n\n%s\n\n%s\n\n%s" %(funDef, v, vcSygus, "(check-synth)"))
	
	logfile = synthDir + basename + '_logs.txt'
	synthLogs = open(logfile,'a')
	#Run synthesis subprocess
	proc = subprocess.Popen([cvcPath, '--lang=sygus2', '--debug-sygus' ,  sygusFile],stdout=synthLogs,stderr=subprocess.DEVNULL)
	
	preds = [p.args[0] for p in predDecls]
	funs = "\n".join(d for d in extractFuns(funDef))
	synthDecls = extractSynth(funDef, preds)
	logfileVerif = open(logfile,"r")
	while(1):
		line = logfileVerif.readline()
		if 'sygus-candidate' in line:
			print("Current PS and INV Guess ", line)
			candidates = "\n".join(d for d in generateCand(synthDecls, line))
			smtFile = synthDir + basename + ".smt"
			with open(smtFile, mode="w") as myfile:
				myfile.write("%s\n\n%s\n\n%s\n\n%s\n\n%s" %(v, funs, candidates, vc, "(check-sat)"))
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
			