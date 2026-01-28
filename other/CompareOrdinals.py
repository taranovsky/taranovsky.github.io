#!/usr/bin/python2
# Author: Dmytro Taranovsky    License:  GPL 2 or later
# This script implements the ordinal notation system described in the paper "Ordinal Notation" by Dmytro Taranovsky, specifically, the one in section "A Stronger Ordinal Notation".  For background, the reader is referred there.

# Briefly, the notation system consists of 0, W (a large ordinal), and a binary function C.  For ordinals in the standard representation written in the postfix form, the comparison is done in the lexicographical order where 'C' < '0' < 'W':  For example, C(C(0,0),0) < C(W, 0) because 000CC < 0WC. (Note: This does not hold for non-standard representations of ordinals).  Of course, the real logic lies in deciding which representations are standard.  Here is a recursive definition.
# 1. '0' and 'W' are standard
# 2. If 'C(a,b)' is standard, then so are 'a' and 'b'.
# 3. If C('a', C('b', 'c')) is standard, then a<=b
# 4. If the above tests succeeded for "C(a,b)", then let T_a be the parse tree of 'a': T_a is the set of subterms of 'a', and for x and y in T_a, x<y means that y is a subterm of x and y!=x.  Let Ord(x) be the ordinal coded by x.  Parse 'a' into the set of terms below W. Formally,
# let X = {x in T_a: Ord(x) < W and forall y<x Ord(y)>=W}
# The test for the standard form is:
# forall x in X forall y>x (Ord(y)<Ord(x) or Ord(y)>=W or thereis z<=y Ord(z) < C(a, b))
# All comparisons between ordinals here can be done in the above-described lexicographical order.
#
# In addition to this definition, we mention some properties of C.
# If a is below the least fixpoint of x->omega^x above b, then C(a, b) = b + omega^a
# Let S_a be the closure of {y: y = C(a, x) for some x}
# C(a, b) is the least ordinal above b that is in S_a
# S_0 consists of all non-zero ordinals in the notation system.
# For limit a, S_a is the intersection of all S_b for b<a
# For every ordinal a, there is an ordinal b<=a such that
# S_{a+1} = lim(S_a) union (S_a intersect b)  (here lim(S_a) is the set of limit points of S_a).
 
import re, sys
if __name__ == "__main__":
	if len(sys.argv) == 2 and sys.argv[1] in ['-h', '-help', '--help']:
		print "Usage: "+sys.argv[0]+" x y"
		print "The script compares x and y where x and y are (codes for) ordinals."
		print "The notation uses two constants: 0 and W, and a binary function C."
		print "x and y should be written in the prefix form.  For example,"
		print "CCW00 (which equals epsilon_0) stands for C(C(Omega, 0), 0)."
		sys.exit()
	if len(sys.argv) != 3:
		print "Error:  The number of arguments must be 2"
		sys.exit(1)

def CheckSyntax(x):  
	"""Returns True x is a valid term and False otherwise"""
	n = 1 # n is the number of arguments that we expect to have
	if not isinstance(x, str):
		return False
	for i in range(len(x)):
		if x[i] not in ['0', 'W', 'C']:
			return False # invalid symbol
		if x[i] == 'C': n+=1
		else: n-=1
		if n == 0: # if we have the exact number of arguments, then return true iff we have reached the end of the string
			return i == len(x)-1
	return False # not enough arguments (or x is empty)

def CompareStd(x, y):
	"""A quick algorithm to compare x and y when they are both in the standard form"""
# If we read the string from right to left, then the comparison between ordinals
# in the standard representation is done in the lexicographic order with C < 0 < W
	x = ''.join(reversed(x))
	y = ''.join(reversed(y))
	return cmp(x.replace('0', 'O'), y.replace('0', 'O'))

def Arg(string, n, startindex=0):
# Assumption: string[startindex:] starts with a valid term x.
# if n = 0, return x
# if n = 1 and x is Cab, return a
# if n = 2 and x is Cab, return b
	nCs = 0 # number of 'C' that we have seen so far
	if n in (0, 1):
		start = startindex + n
	else:
		start = None
	for i in range(startindex, len(string)):
		if n == 2 and start is None and i == startindex + nCs*2 and i > startindex:
			start = i
		if (n != 1 and i == startindex + nCs*2 + 1) or (n == 1 and i == startindex + nCs*2 and i > startindex):
			return string[start:i]
		if string[i] == 'C':
			nCs+=1
	return string[start:]

# Convenient abbreviations
def a1(x): return Arg(x, 1)
def a2(x): return Arg(x, 2)

class ParseTree():
	"""Provides preorder right-to-left traversal of the parse tree of a valid term x.
	<string> is the ordinal term to be parsed, and <index> is the index (in <string>) of the start 
	of the current subterm. <index> is -1 when the traversal has ended."""
	# Note: The user is responsible for ensuring that the requested operations are well-defined
	def __init__(self, string, index=0):
		""""""
		self.string = string
		self.index = index
	def left_item(self):
		return self.index + 1
	def right_item(self):
		return self.index + 1 + len(Arg(self.string, 1, self.index))
	def parent_item(self):
		if self.index == 0:
			return -1
		nCs = 0
		for index in range(self.index-1, -1, -1):
			if self.string[index] == 'C':
				nCs+=1
			if self.index - index - nCs*2 <= 0:
				return index
	def go_left(self):
		self.index = self.left_item()
	def go_right(self):
		self.index = self.right_item()
	def go_up(self):
		self.index = self.parent_item()
	def term(self):
		"""Return the current term"""
		return Arg(self.string, 0, self.index)
	def next(self):
		"""Go to the next term in the right-to-left preorder traversal"""
		if self.string[self.index] == 'C':
			self.go_right()
		else:
			self.skip()
	def skip(self):
		"""Skip subterms of the current term, and go to the next term (in the right-to-left preorder traversal)"""
		index1 = self.index
		self.go_up()
		if self.index == -1:
			return
		while index1 == self.left_item():
			index1 = self.index
			self.go_up()
			if self.index == -1:
				return
		self.go_left()
	
def StandardForm(x, cache=None):
	"""Convert x to the standard form"""
	# We assume that x is a valid term
	# To speed up computation when we call the function multiple times, we keep a cache of the results
	if cache is None:
		cache = {}
	if x in cache:
		return cache[x]
	if x in ['0', 'W']:
		cache[x] = x
		return x
	a = StandardForm(a1(x), cache)
	b = StandardForm(a2(x), cache)
	while b not in ['0', 'W'] and CompareStd(a, a1(b)) == 1:
		b = a2(b) # recursively minimize b
	if a in ('0', 'W') or CompareStd(b, 'W') in (0,1):
		cache[x] = 'C'+a+b
		return 'C'+a+b
	tree1 = ParseTree(a)
	# Parse 'a' in terms of ordinals d < Omega 
	while tree1.term():
		d = tree1.term()
		if CompareStd(d, 'W') != -1:
			tree1.next()
			continue
		# Parse d in terms of ordinals e less than x
		tree2 = ParseTree(d)
		while tree2.term():
			e = tree2.term()
			if CompareStd(e, x) == -1:
				tree2.skip() # do not parse ordinals less than x
			elif CompareStd(e, 'W') == -1 and CompareStd(e, d) == 1:
				# Since d < e < Omega, a is not maximal
				# To maximize a, we replace e with Omega and remove all terms that are to the left of e
				# This works since we are traversing the tree from right to left.			
				a = 'W' + a[tree1.index + tree2.index + len(e):]
				a = (len(a) - a.count('C')*2 - 1)*'C' + a
				a = StandardForm(a, cache) # this is necessary; an example is x='CCCW0CCW00CCW00'
				cache[x] = 'C'+a+b
				return 'C'+a+b
			else:
				tree2.next()
		tree1.skip()
	# At this point, a is maximal in C(a, b)
	cache[x] = 'C'+a+b
	return 'C'+a+b
	
def Compare(x, y, cache=None):
	"""Returns: -1 if x<y, 0 if x==y, 1 if x>y, and 2 if x or y is not a valid term"""
	# <cache> is the cache of results used by StandardForm"""
	if not CheckSyntax(x) or not CheckSyntax(y):
		return 2
	return CompareStd(StandardForm(x, cache), StandardForm(y, cache))

if __name__ == "__main__":
	x = sys.argv[1]
	y = sys.argv[2]
	for arg in (x, y):
		if not CheckSyntax(arg):
			print "Argument "+arg+" is not a valid term"
			sys.exit(1)
	x_std = StandardForm(x)
	if x_std != x:
		print "The standard form of "+x+" is "+x_std+"."
	y_std = StandardForm(y)
	if y_std != y:
		print "The standard form of "+y+" is "+y_std+"."
	result = Compare(x, y)
	if result == -1:
		print x+" < "+y
	elif result == 0:
		print x+" == "+y
	elif result == 1:
		print x+" > "+y
	else:
		print "Comparison failed" # this should not happen
		sys.exit(1)
