#!/usr/bin/env python

###################################
## Plant Generator (2013)
## Author: Josh (JB) Braendel
## 
## A simple L-System interpreter, with a focus on plant
## generating systems
###################################

import bpy
import re 
import random
import math
import string
import mathutils


bl_info = {
    "name": "Plant Generator",
    "author": "Josh Braendel",
    "version": (0, 0, 1),
    "blender": (2, 59, 0),
    "location": "View3D > Add > Curve",
    "description": "Generate a plant based off L-Systems",
    "category": "Add Curve"}


# Verbosity Options
PRINT_RULE      = False
PRINT_RULE_EXEC = False
PRINT_TOKEN     = False
PRINT_OPERATOR  = False
PRINT_DRAWING   = False
PRINT_LIMIT     = False
PRINT_SPECS     = True

# Generator Constraints
MAX_OPERATIONS = 20000 # Limit number of individual operations
MAX_DEPTH      = 300   # Limit branch depth
MIN_DERIVES    = 1000  # Minimum branching (avoids tiny plants)

DRAW_LEAVES  = True
DRAW_FLOWERS = True

# Global (default) Variables in generator
grow_step       = 0.005
grow_radius     = 0.005
grow_angle      = 18
derivations     = 0
operations      = 0
random_max      = 20

states          = []
rules           = []
operator_tokens = ['[',']','&','^','/','\\','!','+','-','F','L','K']
curve           = None
plant           = None



# State
# #####
#
# Current state of generator; branching involves pushing a copy of the 
# current state onto the stack and working with that one, then popping
# it off back to the previous state. State's store a position, 
# orientation and spline which are useful for walking along and
# creating the branch
#########################
class State:
	def __init__(self):
		global curve
		self.position    = (0.0, 0.0, 0.0, 1.0)
		self.orientation = (90.0, 0.0, 00.0) # Facing upwards
		self.spline = curve.splines.new(type='POLY')
	def __repr__(self):
		return "<State position {0}, orientation {1}>".format(self.position, self.orientation)


# Token
# #####
#
# A single item (token) from a grammar in some rule of the L-system;
# this could either be an Operator or another Rule. Executing a token
# involves deriving it down into an array of Operators. For rules
# with a given probability of execution, the token puts this into
# consideration before running the rule
##########################
class Token:
	def __init__(self, rule, param):
		self.rule  = rule
		self.param = param
		if PRINT_RULE:
			print("<Token rule {0}, argument {1}>".format(self.rule, self.param))
	def __repr__(self):
		return "<Token rule {0}, parameter {1}>".format(self.rule, self.param)
	def isOperator(self):
		global operator_tokens
		return self.rule in operator_tokens

	def execute(self,depth):
		global rules, derivations, operations
		global MIN_DERIVES, MAX_OPERATIONS, MAX_DEPTH

		# Derive Token into all Operators
		operators = []
		if operations >= MAX_OPERATIONS:
			if PRINT_LIMIT:
				print("Max Operations: {0} >= {1}".format(str(operations), str(MAX_OPERATIONS)))
			return operators
		if depth > MAX_DEPTH:
			if PRINT_LIMIT:
				print("Max Depth: {0} >= {1}".format(str(depth), str(MAX_DEPTH)))
			return operators

		if self.isOperator():
			operators.append(Operator(self.rule, self.param))
			operations = operations + 1
		else:
			# Find matching rule
			for rule in rules:
				if rule.identifier == self.rule and (self.param == None or (self.param <= rule.arg_max and self.param >= rule.arg_min)):
					if random.random() <= rule.probability or derivations < MIN_DERIVES:

						if derivations < MIN_DERIVES:
							derivations += 1

						# Derive operators for this rule
						new_ops = rule.execute(self.param,depth+1)
						for operator in new_ops:
							operators.append(operator)

		return operators

# Rule Tokenizer & Parser Details
PARSER_RULE        = 1
PARSER_IDENTIFIER  = 2
PARSER_ARGREQ      = 3
PARSER_GRAMMAR     = 4

GRAMMAR_IDENTIFIER = 1
GRAMMAR_ARGUMENT   = 2

# Rule
# ####
#
# A Rule is a piece of the L-System generator which has a provided identifier,
# argument requirement, probability, and grammar. When a Rule is executed, it
# parses through its grammar with the provided (if any) argument, tokenizes
# it, executes each token and then returns the array of operators
#############################
class Rule:
	def __init__(self, description):
		self.rule        = None
		self.identifier  = None
		self.arg_name    = None
		self.arg_max     = None
		self.arg_min     = None
		self.probability = 1
		self.grammar     = ""

		# Tokenize description into rule
		# 	p1 : A(t) : t=7 -> FI(20)[&(60)~L(0)]/(90)[&(45)A(0)]/(90)[&(60)~L(0)]/(90)[&(45)A(4)]FI(10)~K(0)
		tokens = description.split(' ')
		parser = PARSER_RULE
		if PRINT_RULE:
			print("  Token:")
		for token in tokens:
			if token == "":
				continue
			elif token == ":":
				if parser == PARSER_RULE:
					parser = PARSER_IDENTIFIER
				elif parser == PARSER_IDENTIFIER:
					parser = PARSER_ARGREQ
				continue
			elif token == "->":
				parser = PARSER_GRAMMAR
				continue
			if parser == PARSER_RULE:
				self.rule = token
				if token == "w":
					parser = PARSER_GRAMMAR
			elif parser == PARSER_IDENTIFIER:
				# Parse Identifier & Arg
				# 	L(t)
				token_subtokens = token.replace("("," ").replace(")","").split(" ")
				self.identifier = token_subtokens[0]
				self.arg_name   = token_subtokens[1]
			elif parser == PARSER_ARGREQ:
				# parse arg requirements
				#	0.7 * t=7  t<7  t>1   1<t<8
				parts = token.split(':')
				if len(parts) == 2:
					self.probability = float(parts[0])
					token = parts[1]
				else:
					token = parts[0]
				if token == '*':
					self.arg_min = 0
					self.arg_max = 99999999
					continue
				elif token.find('=') > 0:
					token_subtokens = token.split('=')
					self.arg_min = int(token_subtokens[1])
					self.arg_max = int(token_subtokens[1])
					continue
				token_subtokens = token.replace('<',' ').replace('>',' ').split(' ')
				if len(token_subtokens) == 3:
					self.arg_min = int(token_subtokens[0])+1
					self.arg_max = int(token_subtokens[2])-1
				elif token.find('<') >= 0:
					self.arg_min = 0
					self.arg_max = int(token_subtokens[1])-1
				else:
					self.arg_min = int(token_subtokens[1])+1
					self.arg_max = 99999999
			elif parser == PARSER_GRAMMAR:
				self.grammar = token

		if PRINT_RULE:
			print("    Rule: {0}".format(self.rule))
			if self.identifier == None:
				print("    Axiom")
			else:
				print("    Identifier: {0}".format(self.identifier))
			if self.probability < 1:
				print("    Probability: {0}".format(self.probability))
			if isinstance(self.arg_max, (int)) and isinstance(self.arg_min, (int)):
				print("    Argument: {0} >= {1}, {0} <= {2}".format(self.arg_name,self.arg_min,self.arg_max))
			print("    Grammar: {0}".format(self.grammar))
	def __repr__(self):
		return "<Rule [{0}](min {1}, max {2}): {3}".format(self.rule, self.arg_min, self.arg_max, self.grammar)

	def execute(self, arg, depth):
		global random_max

		# Replace argument portions of the grammar with the provided argument
		# 	eg.  A(t+2)  finds (t+2) and replaces 't' with the provided arg,
		# 			evalutes (t+2) and replaces "t+2" with the evaluation
		#
		# Also replaces 'r' with a random number, to add a little randomness
		# to the system
		def replace_exec(match):
			rand = random.random() * random_max
			if random.random() < 0.5: # positive or negative?
				rand *= -1
			return "("+str(eval(match.group(1).replace(str(self.arg_name), str(arg)).replace('r', str(int(rand)))))+")"

		if PRINT_RULE_EXEC:
			print("Executing Rule ({0}): {1}".format(arg, self.grammar))
		exec_grammar = ""
		if self.arg_name == None:
			exec_grammar = self.grammar
		else:
			exec_grammar = re.sub(r'\(([^)]+)\)', replace_exec, self.grammar)
		grammar_tokens = exec_grammar.replace("(","").replace(")","").replace(" ","")
		if PRINT_RULE_EXEC:
			print("Result: {0}".format(grammar_tokens))
		parser = GRAMMAR_IDENTIFIER
		tokens = []

		token_rule = ""
		token_argument = None
		for token in grammar_tokens:
			if parser == GRAMMAR_IDENTIFIER or token.isdigit() == False:
				if token_rule != "":
					tokens.append(Token(token_rule, token_argument))
				token_rule = token
				token_argument = None
				parser = GRAMMAR_ARGUMENT
			elif parser == GRAMMAR_ARGUMENT:
				if token_argument == None:
					token_argument = 0
				token_argument = token_argument * 10 + int(token)
		tokens.append(Token(token_rule, token_argument))

		operators = []
		for token in tokens:
			token_ops = token.execute(depth+1)
			for operator in token_ops:
				operators.append(operator)

		return operators

# Operator
# ########
#
# An Operator is a single operation to be done in the generation process;
# this is anything from growing the stem, pushing or popping states, 
# changing the current direction, or drawing operations (leaves, flowers)
#######################
class Operator:
	def __init__(self, op, arg):
		self.op  = op
		self.arg = arg
		if PRINT_OPERATOR:
			print("<Operator ({0},{1})>".format(self.op, self.arg))
	def __repr__(self):
		return "Operator [{0}]: {1}".format(self.op, self.arg)

	def execute(self):
		global states, curve, grow_step, grow_radius, grow_angle, plant
		global DRAW_LEAVES, DRAW_FLOWERS
		global PRINT_DRAWING

		if self.op == '[':
			# Push State
			newState = State()
			newState.position = states[0].position
			newState.orientation = states[0].orientation
			states.insert(0, newState)

			# Initialize spline
			newState.spline.points[0].co = newState.position
			newState.spline.points[0].radius = grow_radius
			if PRINT_DRAWING:
				print(newState.spline.points)
		elif self.op == ']':
			# Pop State
			# NOTE: spline is attached to curve, so when this state is deleted the spline still exists
			del states[0]
		elif self.op == '+':
			# Rotate + (turn) around Z
			angle = grow_angle
			if self.arg != None:
				angle = int(self.arg)
			orientation = list(states[0].orientation)
			orientation[2] = orientation[2] + angle % 360
			states[0].orientation = tuple(orientation)
		elif self.op == '-':
			# Rotate - (turn) around Z (negative)
			angle = -grow_angle
			if self.arg != None:
				angle = -int(self.arg)
			orientation = list(states[0].orientation)
			orientation[2] = orientation[2] + angle % 360
			states[0].orientation = tuple(orientation)
		elif self.op == '&':
			# Rotate & (pitch) around X
			angle = grow_angle
			if self.arg != None:
				angle = int(self.arg)
			orientation = list(states[0].orientation)
			orientation[0] = orientation[0] + angle % 360
			states[0].orientation = tuple(orientation)
		elif self.op == '^':
			# Rotate ^ (pitch) around X
			angle = -grow_angle
			if self.arg != None:
				angle = -int(self.arg)
			orientation = list(states[0].orientation)
			orientation[0] = orientation[0] + angle % 360
			states[0].orientation = tuple(orientation)
		elif self.op == '/':
			# Rotate / (yaw) around Y
			angle = grow_angle
			if self.arg != None:
				angle = int(self.arg)
			orientation = list(states[0].orientation)
			orientation[1] = orientation[1] + angle % 360
			states[0].orientation = tuple(orientation)
		elif self.op == '\\':
			# Rotate \ (yaw) around Y
			angle = -grow_angle
			if self.arg != None:
				angle = -int(self.arg)
			orientation = list(states[0].orientation)
			orientation[1] = orientation[1] + angle % 360
			states[0].orientation = tuple(orientation)
		elif self.op == 'F':
			# Move forward (default step length)
			step = grow_step
			if self.arg != None:
				step = int(self.arg)
			position = list(states[0].position)
			orientation = list(states[0].orientation)
			position[0] = position[0] + step * math.cos( orientation[0] * math.pi / 180 )
			position[1] = position[1] + step * math.sin( orientation[1] * math.pi / 180 )
			position[2] = position[2] + step * math.cos( orientation[2] * math.pi / 180 )
			states[0].position = tuple(position)
			states[0].spline.points.add(1)
			states[0].spline.points[-1].co = states[0].position
			states[0].spline.points[-1].radius = grow_radius
			if PRINT_DRAWING:
				print("Added Point <{0}>".format(states[0].position))
				print(states[0].spline.points)
				print("Draw..")
		elif self.op == 'L':
			# Draw Leaf
			if DRAW_LEAVES:
				position = list(states[0].position)
				position.pop()

				mesh = bpy.data.meshes.new("Tri")
				p1 = [0,0,0]
				p2 = [0,0,0]
				p3 = [0,0,0]
				leaf_len = 0.04
				raise_len = 0.1
				p1[0] = -leaf_len + position[0]
				p1[1] = -leaf_len + position[1]
				p1[2] = position[2] + random.random()*raise_len

				p2[0] = leaf_len + position[0]
				p2[1] = -leaf_len + position[1]
				p2[2] = position[2] + random.random()*raise_len

				p3[0] = position[0]
				p3[1] = leaf_len + position[1]
				p3[2] = position[2] + random.random()*raise_len

				p1 = tuple(p1)
				p2 = tuple(p2)
				p3 = tuple(p3)
				mesh.from_pydata([p1,p2,p3], [], [(0,1,2)])
				mesh.update()
				ob = bpy.data.objects.new("Tri", mesh)
				ob.data = mesh
				bpy.context.scene.objects.link(ob)
				ob.parent = plant

				if PRINT_DRAWING:
					print("Drawing Leaf: {0}, {1}, {2}".format(p1,p2,p3))
		elif self.op == 'K':
			# Draw Flower
			if DRAW_FLOWERS:
				position = list(states[0].position)
				bpy.ops.mesh.primitive_uv_sphere_add(size=0.01, location=(position[0], position[1], position[2]))
				bpy.context.object.parent = plant
				

				if PRINT_DRAWING:
					print("Draw Flower at <{0}, {1}, {2}>".format(position[0], position[1], position[2]))
		elif self.op == '!':
			# Set radius
			radius = int(self.arg)
		else:
			print("Unknown Operator: {0}".format(self.op))


# Generator
# #########
#
# Generator system for the plant L-System.. This is the class that gets loaded into
# Blender, and is responsible for executing the given generator L-System. Executing
# this (done in the Blender menu, Add > Curves > Generate Plant) will reset the
# generator variables and take the given generator, tokenize & parse it, derive it,
# and execute the list of operators to draw the given plant
###############################
class Generator(bpy.types.Operator):
	bl_idname = "curve.plant_gen"
	bl_label = "PlantGenerator"
	bl_options = {'REGISTER', 'UNDO'}
	axiom  = None

	@classmethod
	def poll(cls, context):
		return True

	def execute(self, context):
		global states, rules, curve, derivations, operations, plant
		global grow_step, grow_radius, grow_angle, random_max, MAX_DEPTH, MAX_OPERATIONS
		global PRINT_SPECS

		context.space_data.show_relationship_lines = False

		# Reset everything
		curve = bpy.data.curves.new("CURVE", type='CURVE')
		curve.dimensions = '3D'
		curve.bevel_depth = 1
		curve.fill_mode = 'FULL'
		curve.resolution_u = 4
		states = [State()]
		rules  = []
		operations = 0
		derivations = 0

		# Deselect ALL of the objects
		for object in bpy.data.objects:
			object.select = False

		#####################
		# L-System Generator
		#
		# The L-System Generator has a list of rules and an axiom (a starting rule). 
		#
		#
		# Rules
		# 	Each rule has 4 components: name, identifier, constraints, grammar
		# 	The axiom only has 2 components: identifier, grammar
		#
		#	G : X					Specifications starts with G
		# 	w : X                   Axiom always starts with w
		# 	p1 : A(t) : * -> X      Rule p1, Identifer A, Argument t, * constraint, X grammar
		#
		#
		# Specifications
		# 	Since each generator may contains wildly different specifications (eg. step rate,
		# 	angle change rate, maximum depth in branching, maximum operations, etc.) I've
		# 	provided the ability to change the default configurations for the generator on
		# 	the first line of the L-System
		# 	G : RADIUS 0.04 STEP 0.3    -> sets a radius of 0.04, step of 0.3
		#
		# 	STEP      -> Growth rate (how much to step forwards in each growth)
		# 	RADIUS    -> Radius of stem
		# 	ANGLE     -> Angle change amount
		#
		# 	RANDOM    -> Maximum random number (used in arguments)
		# 	MAXDEPTH  -> Maximum branching depth
		# 	MAXOPS    -> Maximum number of operations to perform
		#
		#
		# Constraints
		# 	A constrant may have a probability of the given rule executing, and a
		# 	constraint on the argument. If there is no constraint then a * is provided
		# 	0.9:t=7  ->  if t=7 then 0.9 probability of executing; otherwise doesn't execute
		# 	0.34:t<8 ->  if t<8 then 0.34 probability of executing
		# 	0.3:*    ->  0.3 probability of executing
		# 	*        ->  always executes
		#
		#
		# Terminals
		# 	The grammar is made up of a sequence of symbols and terminals. Symbols are calls
		# 	to rules, while terminals are basic operations with pre-defined meanings. Some
		# 	terminals can be called with arguments, but could otherwise leave out the argument
		# 	to use the default instead (eg. default growth step, default angle)
		#
		# 	[   push stack (used for branching)
		# 	]   pop stack
		#
		#	F   grow
		#	L   draw leaf
		#	K   draw flowering bud
		#
		# 	+   turn (right) around Z-axis
		# 	-   turn (left)  around Z-axis
		# 	&   pitch (down) around X-axis
		# 	^   pitch (up)   around X-axis
		# 	/   yaw (right)  around Y-axis
		# 	\   yaw (left)   around Y-axis
		#
		# 	!   set the stem radius
		#
		############################################################


		# The L-System below is taken, and modified, out of pg. 84 of The Algorithmic Beauty of Plants
		# This is supposed to represent a Lychnis coronaria (Rose campion)
		gen_text = """ w :    A(7)
		p1 : A(t) : t=7 -> I(20)[&(60+r)L(0)][^(60+r)L(0)]/(90)[&(45+r)A(0)]/(90)[&(60)L(0)]/(90)[^(45+r)A(4)][&(60)L(0)]I(10)K(0)
		p2 : A(t) : 0.9:t<7 -> FFA(t+1)
		p3 : I(t) : t>0 -> FFI(t-1)
		p4 : L(t) : t=0 -> L(t+1)
		p5 : K(t) : t=0 -> K(t+1) """

		# Taken from (and modified) the link below
		# http://www.nbb.cornell.edu/neurobio/land/OldStudentProjects/cs490-94to95/hwchen/#3D_Tree (Figure 4)
		'''
		gen_text = """ G STEP 0.3 RADIUS 0.005 ANGLE 23 RANDOM 5 MAXDEPTH 10 MAXOPS 10000
		w : FFA
		p1 : A(t) : * -> FF^[^/(20+r)F&\\(20+r)F&\\(20+r)FA]&/(20+r)[&\\(20+r)F^/(20+r)F^/(20+r)FA]A """
		'''


		# Split text into segments of the L-System
		generator_desc = gen_text.splitlines()

		# Parse the specifications (if any) provided
		first_line = generator_desc[0]
		if first_line.strip().split(' ')[0] == "G":
			print("Setting Specifications..")
			# First line is the generator specifications
			specs = first_line.strip().split(' ')
			del specs[0]

			SPEC_PARSE_KEY = 1
			SPEC_PARSE_VAL = 2
			SPEC_STEP      = 1
			SPEC_RADIUS    = 2
			SPEC_ANGLE     = 3
			SPEC_RANDOM    = 4
			SPEC_MAXDEPTH  = 5
			SPEC_MAXOPS    = 6

			spec_parsing = SPEC_PARSE_KEY
			parse_key = None
			for token in specs:
				if spec_parsing == SPEC_PARSE_KEY:
					if token == "STEP":
						parse_key = SPEC_STEP
					elif token == "RADIUS":
						parse_key = SPEC_RADIUS
					elif token == "ANGLE":
						parse_key = SPEC_ANGLE
					elif token == "RANDOM":
						parse_key = SPEC_RANDOM
					elif token == "MAXDEPTH":
						parse_key = SPEC_MAXDEPTH
					elif token == "MAXOPS":
						parse_key = SPEC_MAXOPS
					else:
						parse_key = None
					spec_parsing = SPEC_PARSE_VAL
				elif spec_parsing == SPEC_PARSE_VAL:
					val = float(token)
					if parse_key == SPEC_STEP:
						if PRINT_SPECS:
							print("Grow Step: {0}".format(str(val)))
						grow_step = val
					elif parse_key == SPEC_RADIUS:
						if PRINT_SPECS:
							print("Radius: {0}".format(str(val)))
						grow_radius = val
					elif parse_key == SPEC_ANGLE:
						if PRINT_SPECS:
							print("Angle: {0}".format(str(val)))
						grow_angle = val
					elif parse_key == SPEC_RANDOM:
						if PRINT_SPECS:
							print("Max Random: {0}".format(str(val)))
						random_max = val
					elif parse_key == SPEC_MAXDEPTH:
						if PRINT_SPECS:
							print("Max Depth: {0}".format(str(val)))
						MAX_DEPTH = val
					elif parse_key == SPEC_MAXOPS:
						if PRINT_SPECS:
							print("Max Operations: {0}".format(str(val)))
						MAX_OPERATIONS = val
					parse_key = None
					spec_parsing = SPEC_PARSE_KEY
			del generator_desc[0]

		# Go through each line of the L-System; parse the rule and add it to the list of rules
		for line in generator_desc:
			rule = Rule(line.strip())
			if rule.identifier == None:
				self.axiom = rule
			else:
				rules.append(rule)

		# Draw the curve
		plant = bpy.data.objects.new("Plant", curve)
		bpy.context.scene.objects.link(plant)

		# Execute the Axiom
		operators = self.axiom.execute(0,0)
		for operator in operators:
			operator.execute()

		print("Operators: {0}".format(len(operators)))
		return {'FINISHED'}

	def __repr__(self):
		return "The Generator"




#################################################################
## BLENDER
##
## Setup stuff for loading this script into Blender
## Find in menu; Add > Curve > Generate Plant

def menu_func(self, context):
    self.layout.operator(Generator.bl_idname, text="Generate Plant")


def register():
	bpy.utils.register_class(Generator)
	bpy.types.INFO_MT_curve_add.append(menu_func)


def unregister():
	bpy.types.INFO_MT_curve_add.remove(menu_func)
	bpy.utils.unregister_class(Generator)


if __name__ == "__main__":
    register()
