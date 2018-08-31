"""
(C) Copyright 2018 CERN and University of Manchester.
This software is distributed under the terms of the GNU General Public Licence version 3 (GPL Version 3), copied verbatim in the file "COPYING".
In applying this licence, CERN does not waive the privileges and immunities granted to it by virtue of its status as an Intergovernmental Organization or submit itself to any jurisdiction.

Author: Joshua Dawes - CERN, University of Manchester - joshua.dawes@cern.ch
"""

import argparse
import traceback
import ast
from datetime import datetime
from pprint import pprint

import sqlite3
import json

# import output functions
from control_flow_graph.construction import *
from verdict_reports import VerdictReport

monitor_time_series = []

verbose = False
verbose_monitor = False
optimised_monitor = False
apply_verification = False
can_stop = False
db = None
check_monitor_size = False

# a map from static qd indices to the list of monitors
# currently instantiated for that static qd element
static_qd_to_monitors = {}
# a map from static bindings to monitor configurations under which the monitor reached a verdict
# this likely to be memory intensive - I want to find another way to monitor
static_bindings_to_monitor_states = {}

# a map from static bindings to instrumentation points that were the most recent
# to trigger monitor instantiation.
static_bindings_to_trigger_points = {}

# binding space - statically computed
bindings = []

# dicts will be inserted here when certain events happen
# this is for checking efficiency
timing_points = []

# dicts will be inserted here of the form (qd_index:..., list_index:..., size:..., timestamp:...)
# meaning the monitor at the index 'list_index' in the list of monitors
# active for the qd at 'qd_index' has size 'size'
monitor_sizes = []

timing_point_lock = threading.Lock()
monitor_sizes_lock = threading.Lock()

def add_timing_point(event):
	timing_point_lock.acquire()
	timing_points.append({"event": event, "timestamp" : datetime.datetime.now()})
	timing_point_lock.release()

def add_monitor_size_point(qd_index, list_index, size, sub_verdict, context):
	monitor_sizes_lock.acquire()
	monitor_sizes.append({"qd_index" : qd_index, "list_index" : list_index, "size" : size, "sub_verdict" : sub_verdict, "context": context, "timestamp" : datetime.datetime.now()})
	monitor_sizes_lock.release()

def scfg_to_tree(root):
	"""
	Given a root vertex, compute the set of vertices and edges reachable from that
	vertex in the scfg.
	"""
	reachable_set = []
	traversal_stack = [root]
	traversed_edges = []
	while len(traversal_stack) > 0:
		top_vertex = traversal_stack.pop()
		for edge in top_vertex.edges:
			if not(edge in traversed_edges):
				reachable_set.append(edge)
				reachable_set.append(edge._target_state)
				traversed_edges.append(edge)
				traversal_stack.append(edge._target_state)
	return reachable_set

def construct_reachability_map(scfg):
	"""
	For each vertex in the scfg given, do a depth-first search
	"""

	vertex_to_reachable_set = {}

	for vertex in scfg.vertices:
		reachable_set = scfg_to_tree(vertex)
		vertex_to_reachable_set[vertex] = reachable_set

	return vertex_to_reachable_set


def compute_binding_space(quantifier_sequence, scfg, reachability_map, current_binding=[]):
	"""
	Given a sequence of quantifers over symbolic states/edges in the given scfg,
	compute the space of bindings that can be given to the formula to which this quantifier sequence is applied.
	The current_binding given may be partial, but represents the current point in the space of bindings upto which we have traversed.
	"""

	if len(current_binding) == 0:
		# we've just started - compute the static qd for the first quantifier,
		# then iterate over it and recurse into the list of quantifiers for each element
		if type(quantifier_sequence._bind_variables[0]) is StaticState:
			variable_changed = quantifier_sequence._bind_variables[0]._name_changed
			qd = filter(lambda symbolic_state : symbolic_state._name_changed == variable_changed or variable_changed in symbolic_state._name_changed, scfg.vertices)
		elif type(quantifier_sequence._bind_variables[0]) is StaticTransition:
			variable_operated_on = quantifier_sequence._bind_variables[0]._operates_on
			relevant_target_vertices = filter(
				lambda symbolic_state : symbolic_state._name_changed == variable_operated_on or variable_operated_on in symbolic_state._name_changed,
				scfg.vertices
			)
			qd = map(lambda symbolic_state : symbolic_state._previous_edge, relevant_target_vertices)

		print("computed independent qd: %s" % qd)
		# for now don't handle transitions
		"""elif type(quantifier_sequence._bind_variables[0]) is StaticTransition:
			operated_on = quantifier_sequence._bind_variables[0]._operates_on"""
		binding_space = []
		# recurse with (possibly partial) bindings
		for element in qd:
			binding_space += compute_binding_space(quantifier_sequence, scfg, reachability_map, [element])

		print("computed whole binding space")
		return binding_space
	elif len(current_binding) < len(quantifier_sequence._bind_variables):
		# we have a partial binding
		# find the next quantifier
		next_index = len(current_binding)
		next_quantifier = quantifier_sequence._bind_variables[next_index]
		# find the position in the quantifier sequence on which the next quantifier depends
		index_in_quantifier_sequence = quantifier_sequence._bind_variables.index(next_quantifier._required_binding)
		# get the current value at that position in the binding we have
		current_binding_value = current_binding[index_in_quantifier_sequence]
		# use the type of the qd we need to traverse the scfg from this point
		if type(next_quantifier) is StaticState:
			print("computing unbounded future states according to %s" % next_quantifier)
		elif type(next_quantifier) is StaticTransition:
			print("computing unbounded future transitions according to %s using binding %s" % (next_quantifier, current_binding))
			# only works for vertex inputs
			# this has to cater for edges that are both assignments and function calls (assignments of function call return values)
			qd = filter(lambda edge : hasattr(edge, "_operates_on") and \
				(edge._operates_on == next_quantifier._operates_on or next_quantifier._operates_on in edge._operates_on), reachability_map[current_binding_value])

			# compute the bindings from this new qd
			binding_space = []
			for element in qd:
				binding_space += compute_binding_space(quantifier_sequence, scfg, reachability_map, current_binding + [element])
			return binding_space
	else:
		# we now have a complete binding - return it
		return [current_binding]

def import_property_definition(file_name):
	"""
	Given a file name, read in the Python code and execute it.
	We do this so nothing has to be imported in the property definition code.
	We assume the property is stored in a variable called formula_structure.
	It might be better to just expect property definitions to import things, rather
	than using exec here...
	"""
	code = "".join(open(file_name, "r").readlines())
	exec(code)
	return formula_structure

steps = 0

def output_graph_with_highlight(thing_to_highlight):
	global args
	global steps
	output_file = "%s-run-%i.gv" % (args.graph[0].replace(".gv", ""), steps)
	graph = Digraph()
	graph.attr("graph", splines="true", fontsize="10")
	shape = "circle"
	for vertex in new_scfg.vertices:

		if vertex == thing_to_highlight:
			colour = "red"
		else:
			colour = "white"

		graph.node(str(id(vertex)), vertex._name_changed, shape=shape, style="filled", fillcolor=colour)

		for edge in vertex.edges:
			if edge == thing_to_highlight:
				stroke = "red"
			else:
				stroke = None

			graph.edge(
				str(id(vertex)),
				str(id(edge._target_state)),
				"%s : %s" % (str(edge._condition), instruction_to_string(edge._instruction)),
				color=stroke
			)
	graph.render(output_file)
	# increment the number of steps
	steps += 1

if __name__ == "__main__":

	parser = argparse.ArgumentParser(description='Read in a sample program, instrument it for a property, and run it with monitoring.')
	parser.add_argument('--program', type=str, nargs=1, help='The filename in which the program to instrument and run is found.', required=True)
	parser.add_argument('--graph', type=str, nargs=1, help='The filename of the graph to output.', required=False)
	parser.add_argument('--optimised-monitor', action='store_true', help='If supplied, use optimised monitor update.')
	parser.add_argument('--verify', action='store_true', help='If supplied, apply verification.')
	parser.add_argument('--db', type=str, required=True, help='The database to write the log to - we use this for performance analysis of the monitoring.')
	parser.add_argument('--property', type=str, required=True, help='The file in which the property definition is found for verification.')
	parser.add_argument('--check-monitor', action='store_true', help='If supplied, the monitor size will be tracked.')
	parser.add_argument('--generate-vis-data', action='store_true', help='If supplied, data will be generated that can be used by the visualisation tool.')

	args = parser.parse_args()
	optimised_monitor = args.optimised_monitor
	apply_verification = args.verify
	db = args.db
	check_monitor_size = args.check_monitor

	print("MONITOR CHECKING: %s" % str(check_monitor_size))

	# read in a sample program
	try:
		code = "".join(open(args.program[0], "r").readlines())
	except Exception as e:
		traceback.print_exc()
		print("Couldn't open the program file.")
		exit()

	ast_obj = ast.parse(code)

	# a function used in the imported code
	def f(a): print("***************f is executing with input %f*******************" % a);time.sleep(a);
	def g(a): print("g is called!!"); time.sleep(a/10)
	def database_operation(db): time.sleep(0.5)
	def close_connection(db): time.sleep(0.5)
	def operation(t): time.sleep(t)
	def query(type, data): time.sleep(0.3 + 0.2*len(data)); return []
	def new_lock(): return# instantaneous for now

	if not(apply_verification):
		# just run the code object normally
		exec(compile(ast_obj, filename="<ast>", mode="exec"))

		# exit without performing any verification
		exit()

	program_start_time = datetime.datetime.now()

	top_level_block = ast_obj.body

	new_scfg = CFG()

	print("="*100)
	print("CONSTRUCTING SCFG")
	print("="*100)
	final_vertices = new_scfg.process_block(top_level_block)
	print("="*100)

	add_timing_point("constructed cfg")

	# put the graph into a dot file
	#output_file = "control_flow_graph/cfg.gv"
	if args.graph:
		output_file = args.graph[0]
		graph = Digraph()
		graph.attr("graph", splines="true", fontsize="10")
		shape = "circle"
		for vertex in new_scfg.vertices:
			graph.node(str(id(vertex)), str(vertex._name_changed), shape=shape)
			for edge in vertex.edges:
				graph.edge(
					str(id(vertex)),
					str(id(edge._target_state)),
					"%s : %s" % (str(edge._condition), instruction_to_string(edge._instruction))
				)
		graph.render(output_file)
		print("Writing SCFG to file '%s'." % output_file)
	else:
		print("No file given to write SCFG to - not writing one.")

	print("="*100)

	#pprint(reachability_map)

	# set up a sample QD, find the edges or vertices that correspond to its elements in the CFG
	# the QD for now is the set of all states that modify a.

	# REMEMBER: in instrumentation, use the name referred to in the atom to decide which value to record
	# Note: this qd is static, hence does not represent all runtime states if there are loops
	# in the program.
	#static_qd = filter(lambda vertex : vertex._name_changed == "a", new_scfg.vertices)

	add_timing_point("constructed static qd")
	# this map will send qd element indices to maps from
	# bind variable indices to the sequence of points in the program
	# that are needed to evaluate the formula for that element in the qd,
	# and that specific index in the binding
	static_qd_to_point_map = {}

	# define a formula
	formula_structure = import_property_definition(args.property)

	print(formula_structure._formula_atoms)

	print(formula_structure)

	add_timing_point("set up formula")

	atoms = formula_structure._formula_atoms

	# for each element in the static QD, compute the states/transitions
	# needed to determine the truth values of the atoms

	print("="*100)
	print("INSTRUMENTING INPUT PROGRAM")
	print("="*100)

	# from the sequence of quantifiers, compute the static space of bindings.
	reachability_map = construct_reachability_map(new_scfg)
	bindings = compute_binding_space(formula_structure, new_scfg, reachability_map)

	print("Finished computing static space of bindings.")
	print("Space has %i bindings." % len(bindings))

	"""for binding in bindings:
		call = binding[1]._instruction
		print(binding[0].edges, call.value.args[0].n)"""

	print("bindings", bindings)

	"""
	This loop will remain roughly the same, except where each element
	is now a tuple taken from the binding space generated from the sequence of quantifiers.

	For each atom, find the component of the binding that it depends on
	and apply the composition to this one.

	We find the component of the binding by finding the input bind variable
	for the atom, finding the position in the quantifier sequence of that input
	and use that position in the current binding.

	We must also build up a map from bind variables to their instrumentation points.
	These sets will form a partition of the whole set of instrumentation points
	for a binding.
	"""

	#for (m, element) in enumerate(static_qd):
	for (m, element) in enumerate(bindings):
		#print("starting from vertex changing %s" % element._name_changed)
		#element_instrumentation_points = []

		print("PROCESSING BINDING %s" % element)
		element_types = []

		add_timing_point("beginning processing for qd element %i" % m)

		static_qd_to_point_map[m] = {}

		for atom in atoms:

			add_timing_point("beginning processing for atom %s" % atom)

			composition_sequence = derive_composition_sequence(atom)

			input_bind_variable = composition_sequence[-1]

			print("atom %s has input bind variable %s" % (atom, input_bind_variable))

			position_in_quant_sequence = formula_structure._bind_variables.index(input_bind_variable)
			value_from_binding = element[position_in_quant_sequence]

			print("using value %s from index %i of binding %s" %\
				(value_from_binding, position_in_quant_sequence, element))

			add_timing_point("derived composition sequence")
			# the first element tells us how to instrument (variable value, function call duration, etc)
			# the final element tells us the bind variable to navigate from
			# the intermediate elements tell us what to look for in the control flow graph, starting from
			# the bind variable
			moves = list(reversed(composition_sequence[1:-1]))
			print("atom and moves: ", atom, moves)

			# iterate through the moves we have to make,
			# using the type of the operator used in the move to compute the points we have to instrument
			# we set the default set to include just the current binding
			# for the case where no transformation happens
			instrumentation_points = [value_from_binding]
			# currently only works for a single move
			# for multiple moves we need to apply the transformation to each "previous" instrumentation point
			"""
			At the moment, this code is wrong - it's supposed to take as input the previous round of results,
			but always take the first round - needs to be changed.
			Will do when I consider nested future time operators.
			"""
			for move in moves:
				if type(move) is NextStaticTransition:
					print("computing next transitions operating on %s from %s for %s" % (move._operates_on, move._centre, move))
					calls = []
					if type(value_from_binding) is CFGVertex:
						new_scfg.next_calls(value_from_binding, move._operates_on, calls, marked_vertices=[])
					elif type(value_from_binding) is CFGEdge:
						new_scfg.next_calls(value_from_binding._target_state, move._operates_on, calls, marked_vertices=[])
					print("next calls to %s are " % move._operates_on, calls)
					instrumentation_points = calls

			#instrumentation_points += instrumentation_points
			#atoms += [atom] * len(instrumentation_points)

			add_timing_point("derived instrumentation points based on atoms")

			# add the pair consisting of the instrumentation points and the original atom
			#  to the point in the map identified by (static binding, index in static binding)
			if static_qd_to_point_map[m].get(position_in_quant_sequence):
				static_qd_to_point_map[m][position_in_quant_sequence].append((instrumentation_points, atom))
			else:
				static_qd_to_point_map[m][position_in_quant_sequence] = [(instrumentation_points, atom)]

			static_qd_to_point_map[m][position_in_quant_sequence].append(([value_from_binding], "trigger"))

		"""# store the map from the current static qd index,
		# to all of the points that must be instrumented
		static_qd_to_point_map[m] = element_instrumentation_points"""

		add_timing_point("beginning instrumentation")

		# now, perform the instrumentation
		# iterate through the bind variables - for each bind variable, instrument its points.

		for bind_variable_index in static_qd_to_point_map[m].keys():
			for (atom_index, point_atom_pair) in enumerate(static_qd_to_point_map[m][bind_variable_index]):
				points = point_atom_pair[0]
				atom = point_atom_pair[1]

				if atom == "trigger":
					# we must instrument this as a trigger point
					print("instrumenting a trigger point")
					point = points[0]

					# this instrument only needs to reset the minimality flag for the correct partition set
					# the binding space index combined with the bind variable index are enough for that
					instrument = "queue.put((%i, %i))" % (m, bind_variable_index)

					instrument_ast = ast.parse(instrument).body[0]
					if type(point) is CFGVertex:
						instruction = point._previous_edge._instruction
					else:
						instruction = point._instruction

					lineno = instruction.lineno
					col_offset = instruction.col_offset

					index_in_block = instruction._parent_body.index(instruction)

					instruction._parent_body.insert(index_in_block+1, instrument_ast)

				else:

					for (n, point) in enumerate(points):
						if type(atom) is formula_tree.TransitionDurationInInterval:
							print("instrumenting call to measure duration")
							print("instrumenting instrumentation point %s on line %i" % (point, point._instruction.lineno))


							timer_start_statement = "__timer_s = datetime.datetime.now()"
							timer_end_statement = "__timer_e = datetime.datetime.now()"
							# we put a pair (index in static qd, index in instrumentation points)
							# this determines the point in the static cfg that will be executed
							time_difference_statement = ("__duration = __timer_e - __timer_s; queue.put((%i, %i, %i, %i, __duration, %i, %i));" +\
														"print('instrument firing!', %i, %i, list(queue.queue));") %\
								(m, bind_variable_index, atom_index, n, atoms.index(atom), point._instruction.lineno, m, bind_variable_index)

							# timing instruction - helps with performance analysis
							timing_point_statement = "add_timing_point('instrumented instruction on line %i')" % point._instruction.lineno

							start_ast = ast.parse(timer_start_statement).body[0]
							end_ast = ast.parse(timer_end_statement).body[0]
							difference_ast = ast.parse(time_difference_statement).body[0]
							queue_ast = ast.parse(time_difference_statement).body[1]
							print_ast = ast.parse(time_difference_statement).body[2]
							timing_point_ast = ast.parse(timing_point_statement).body[0]

							add_timing_point("constructed asts for transition duration instrument")

							start_ast.lineno = point._instruction.lineno
							start_ast.col_offset = point._instruction.col_offset
							end_ast.lineno = point._instruction.lineno
							end_ast.col_offset = point._instruction.col_offset
							difference_ast.lineno = point._instruction.lineno
							difference_ast.col_offset = point._instruction.col_offset

							print_ast.lineno = point._instruction.lineno
							print_ast.col_offset = point._instruction.col_offset

							queue_ast.lineno = point._instruction.lineno
							queue_ast.col_offset = point._instruction.col_offset
							timing_point_ast.lineno = point._instruction.lineno
							timing_point_ast.col_offset = point._instruction.col_offset

							#ast.increment_lineno(point._instruction, n=2)

							index_in_block = point._instruction._parent_body.index(point._instruction)

							# instruments are added in reverse order
							point._instruction._parent_body.insert(index_in_block+1, timing_point_ast)
							point._instruction._parent_body.insert(index_in_block+1, print_ast)
							point._instruction._parent_body.insert(index_in_block+1, queue_ast)
							point._instruction._parent_body.insert(index_in_block+1, difference_ast)
							point._instruction._parent_body.insert(index_in_block+1, end_ast)
							point._instruction._parent_body.insert(index_in_block, start_ast)

							add_timing_point("modified program with transition duration instrument")

							print("PARENT BODY")
							print(point._instruction._parent_body)

						elif type(atom) is formula_tree.StateValueInInterval:
							print("instrumenting state changes")
							#print(point._previous_edge._instruction)
							#print("instrumenting instrumentation point %s on line %i" % (point, point._previous_edge._instruction.lineno))

							# we are instrumenting a state, so store the value used in that state
							# in a new variable by accessing the existing variable
							# we place code in the edge leading to this vertex, since
							# that is the edge that contains the code that computes the state
							# this vertex models.

							incident_edge = point._previous_edge
							parent_block = incident_edge._instruction._parent_body

							# need to adjust this to record the entire state! <- possibly infeasible
							record_state = "record_state_%s = %s; queue.put((%i, %i, %i, %i, {'%s' : record_state_%s}, %i, %i));" %\
								(atom._name, atom._name, m, bind_variable_index, atom_index, n, atom._name, atom._name, atoms.index(atom), incident_edge._instruction.lineno)

							# timing instruction - helps with performance analysis
							timing_point_statement = "add_timing_point('instrumented state change on line %i')" % incident_edge._instruction.lineno

							record_state_ast = ast.parse(record_state).body[0]
							queue_ast = ast.parse(record_state).body[1]
							timing_point_ast = ast.parse(timing_point_statement).body[0]

							timing_point_ast.lineno = incident_edge._instruction.lineno
							timing_point_ast.col_offset = incident_edge._instruction.col_offset

							record_state_ast.lineno = incident_edge._instruction.lineno
							record_state_ast.col_offset = incident_edge._instruction.col_offset

							queue_ast.lineno = incident_edge._instruction.lineno
							queue_ast.col_offset = incident_edge._instruction.col_offset

							add_timing_point("constructed ast for state instrument")

							index_in_block = parent_block.index(incident_edge._instruction)
							parent_block.insert(index_in_block+1, record_state_ast)
							parent_block.insert(index_in_block+2, timing_point_ast)
							parent_block.insert(index_in_block+3, queue_ast)

							add_timing_point("modified program with state instrument")

	def program_thread_f(new_code_obj):
		global can_stop

		print("EXECUTING INSTRUMENTED CODE")
		print("="*50)
		add_timing_point("starting instrumented code inside thread")
		exec(new_code_obj)
		print("="*50)
		print("ENDING EXECUTION OF INSTRUMENTED CODE")

		can_stop = True

	def consumer_thread_f():
		"""
		Function to be run by consumer thread.
		"""
		global static_qd
		global static_qd_to_point_map
		# temporary
		global atoms
		global can_stop
		global static_qd_to_monitors
		global bindings

		global verdict_report

		while not(can_stop) or (can_stop and not(queue.empty())):
			# take top element from the queue
			try:
				top_pair = queue.get(timeout=1)
			except:
				print("queue empty - not attempting consumption")
				continue

			print("="*100)

			print("CONSUMING ", top_pair)
			print("queue is now %s" % str(queue.queue))

			add_timing_point("beginning consumption of tuple %s" % str(top_pair))

			# left element of the pair is the index in the static qd
			# right element is the index of the instrumentation point
			# in the set of instrumentation points required for that member
			# of the static qd

			if len(top_pair) == 2:
				# we've received a trigger instrument
				static_qd_index = top_pair[0]
				bind_variable_index = top_pair[1]

				if not(static_bindings_to_trigger_points.get(static_qd_index)):
					static_bindings_to_trigger_points[static_qd_index] = {}

				# reset the trigger
				if static_bindings_to_trigger_points[static_qd_index].get(bind_variable_index):
					static_bindings_to_trigger_points[static_qd_index][bind_variable_index] = None

				print("Set partition set trigger for static qd %i and bind variable index %i to None" % (static_qd_index, bind_variable_index))

				# continue onto the next iteration of the consumption loop
				# trigger instrumentation points don't contribute to the monitor state
				continue

			static_qd_index = top_pair[0]
			bind_variable_index = top_pair[1]
			atom_index = top_pair[2]
			instrumentation_set_index = top_pair[3]
			observed_value = top_pair[4]# this may be redundant now
			associated_atom = atoms[top_pair[5]]


			# use the atom with the observed value and the object in the static cfg to decide
			# on the value of the atom and update the corresponding monitor

			# NOTE: THIS ASSUMES THAT EACH INSTRUMENT IS FOR ONE BINDING - THIS WILL PROBABLY
			# CHANGE AT SOME POINT SINCE THERE IS INTERSECTION IN INSTRUMENTATION SETS
			# BETWEEN BINDINGS.

			instrumentation_set = static_qd_to_point_map[static_qd_index][bind_variable_index][atom_index]

			instrumentation_point = instrumentation_set[0][instrumentation_set_index]
			instrumentation_atom = instrumentation_set[1]

			# if we have to generate visulisation data,
			# output a graph with the instrumentation point highlighted
			if args.generate_vis_data:
				output_graph_with_highlight(instrumentation_point)

			print(instrumentation_point, static_qd_index)

			# for now, instruments point to single qd bindings so no need to compute a set
			# of valid binding indices

			pprint(static_qd_to_point_map[static_qd_index][bind_variable_index])

			# get all the instrumentation points associated with bind_variable_index
			"""relevant_instrumentation_points = []
			for pair in static_qd_to_point_map[static_qd_index][bind_variable_index]:
				relevant_instrumentation_points += pair[0]"""

			#print("relevant instrumentation points", relevant_instrumentation_points)
			print("instrumentation point received from", instrumentation_point)

			# decide what instrumentation_point can trigger (monitor update, new monitor, or nothing at all)
			# for now the criteria is whether it is the first element in the list
			# this is a temporarily primitive implementation of the partial order-based condition

			# decide if the instrumentation point is branch minimal
			# we need to get the trigger point for the relevant partition
			if static_bindings_to_trigger_points.get(static_qd_index):
				if static_bindings_to_trigger_points.get(static_qd_index).get(bind_variable_index):
					# the trigger point is not None, so branch minimality is not attained
					branch_minimal = False
				else:
					# the trigger is None, so branch minimality is attained - set the trigger point to the
					# current instrumentation point to remove branch minimality
					branch_minimal = True
					static_bindings_to_trigger_points[static_qd_index][bind_variable_index] = instrumentation_point
			else:
				# no monitors exist for this qd - branch minimality is attained
				# I don't think it's possible to get to this branch, actually...
				branch_minimal = True
				static_bindings_to_trigger_points[static_qd_index] = {}
				static_bindings_to_trigger_points[static_qd_index][bind_variable_index] = instrumentation_point

			print("BRANCH MINIMAL:", branch_minimal)

			#if relevant_instrumentation_points[0] == instrumentation_point:
			if branch_minimal:
				print("USING STATIC QD INDEX %i" % static_qd_index)
				# the instrumented point is the first in the list for this point in the qd
				# we now check for existing monitors associated with this instrumentation point
				monitors = static_qd_to_monitors.get(static_qd_index)

				print(monitors)

				if monitors is None or list(set(monitors)) == [None]:

					print("No monitors exist - instantiating new ones")
					# there is no monitor for this element of the qd - instantiate a new one for every
					# configuration found for monitors corresponding to the prefix of the binding before bind_variable_index

					# if we're dealing with the first bind variable, there cannot be previous configurations
					# so in that case just instantiate a new monitor
					# THIS CODE NEEDS TO BE REFACTORED

					if bind_variable_index == 0:

						print("instantiating new monitor for static qd index %i" % static_qd_index)
						#new_monitor = formula_tree.new_monitor(If(atom1).then(formula_tree.land(atom2, atom3)))
						#new_monitor = formula_tree.new_monitor(If(atom1).then(atom2))
						new_monitor = formula_tree.new_monitor(formula_structure.get_formula_instance())
						static_qd_to_monitors[static_qd_index] = [new_monitor]

						add_timing_point("instantiated first monitor for static qd index %i" % static_qd_index)

						# update the monitor with the newly observed data
						sub_verdict = new_monitor.process_atom_and_value(associated_atom, observed_value)
						if sub_verdict == True or sub_verdict == False:

							# record the monitor state with the binding
							if static_bindings_to_monitor_states.get(static_qd_index) is None:
								static_bindings_to_monitor_states[static_qd_index] = [new_monitor._state]
							elif not(new_monitor._state in static_bindings_to_monitor_states[static_qd_index]):
								static_bindings_to_monitor_states[static_qd_index].append(new_monitor._state)

							pprint(static_bindings_to_monitor_states)

							# set the monitor to None
							static_qd_to_monitors[static_qd_index] = [None]
							print("TRUE OR FALSE VERDICT REACHED")
							add_timing_point("verdict reached - monitor deleted")
							#add_monitor_size_point(static_qd_index, 0, 0, sub_verdict, "new")

							verdict_report.add_verdict(static_qd_index, sub_verdict)
						else:
							print("NO VERDICT REACHED")
							add_timing_point("processed observed value '%s' for atom %s" % (observed_value, associated_atom))
							#add_monitor_size_point(static_qd_index, 0, len(new_monitor.get_unresolved_atoms()), sub_verdict, "new")

					else:

						stored_bindings = static_bindings_to_monitor_states.keys()
						# get bindings with matching prefixes
						relevant_bindings = filter(
							lambda stored_binding : bindings[stored_binding][0:bind_variable_index-1] ==\
								bindings[static_qd_index][0:bind_variable_index-1],
							stored_bindings)

						print("relevant bindings:")
						pprint(relevant_bindings)
						print("from:")
						pprint(stored_bindings)

						# for each of the relevant bindings, find the configurations of atoms for monitors
						# that have existed for those bindings, and instantiate new monitors, replacing the atom we have now

						configurations = []
						for relevant_binding in relevant_bindings:
							configurations += static_bindings_to_monitor_states[relevant_binding]

						print("configurations:", configurations)

						for (n, configuration) in enumerate(configurations):

							configuration = configuration._state

							print("PROCESSING CONFIGURATION %s" % configuration)

							print("instantiating new monitor for static qd index %i" % static_qd_index)
							#new_monitor = formula_tree.new_monitor(If(atom1).then(formula_tree.land(atom2, atom3)))
							#new_monitor = formula_tree.new_monitor(If(atom1).then(atom2))
							new_monitor = formula_tree.new_monitor(formula_structure.get_formula_instance())
							if n == 0:
								static_qd_to_monitors[static_qd_index] = [new_monitor]
							else:
								static_qd_to_monitors[static_qd_index].append(new_monitor)

							add_timing_point("instantiated first monitor for static qd index %i" % static_qd_index)

							print("UPDATING NEW MONITOR WITH CONFIGURATION")

							# update the new monitor for this configuration with all the atoms apart from the one we've
							# just observed

							for key in configuration.keys():
								if not(key == associated_atom) and not(key == formula_tree.lnot(associated_atom)):
									print("%s IS NOT OBSERVED ATOM %s - UPDATING NEW MONITOR WITH IT" % (key, associated_atom))
									if configuration[key] == True:
										new_monitor.check_optimised(key)
									elif configuration[key] == False:
										new_monitor.check_optimised(formula_tree.lnot(key))
									else:
										# the value is None - it wasn't observed in this configuration
										pass
								else:
									print("%s IS OBSERVED ATOM %s - NOT USING IT" % (key, associated_atom))

							# update the monitor with the newly observed data
							sub_verdict = new_monitor.process_atom_and_value(associated_atom, observed_value)
							if sub_verdict == True or sub_verdict == False:

								# record the monitor state with the binding
								if static_bindings_to_monitor_states.get(static_qd_index) is None:
									static_bindings_to_monitor_states[static_qd_index] = [new_monitor._state]
								elif not(new_monitor._state in static_bindings_to_monitor_states[static_qd_index]):
									static_bindings_to_monitor_states[static_qd_index].append(new_monitor._state)

								#pprint(static_bindings_to_monitor_states)

								# set the monitor to None
								static_qd_to_monitors[static_qd_index] = [None]
								print("TRUE OR FALSE VERDICT REACHED")
								add_timing_point("verdict reached - monitor deleted")
								#add_monitor_size_point(static_qd_index, 0, 0, sub_verdict, "new")

								verdict_report.add_verdict(static_qd_index, sub_verdict)
							else:
								print("NO VERDICT REACHED")
								add_timing_point("processed observed value '%s' for atom %s" % (observed_value, associated_atom))
								#add_monitor_size_point(static_qd_index, 0, len(new_monitor.get_unresolved_atoms()), sub_verdict, "new")

				else:
					# there is a monitor:
					# If the atom is derive from the first binding:
					# if we're observing the data again - instantiate a new one
					# if there is already a monitor, it must have observed this data since the only
					# way for it to exist, for now, is for its instantiation to be triggered
					# by the execution of this point

					# If the atom is derived from any other bind variable, then just update the monitors

					if bind_variable_index == 0:
						# first bind variable - we assume for now that this always triggers instantiation
						# this may need to change later - we'll see
						print("instantiating new monitor for static qd index %i" % static_qd_index)
						#new_monitor = formula_tree.new_monitor(If(atom1).then(formula_tree.land(atom2, atom3)))
						#new_monitor = formula_tree.new_monitor(If(atom1).then(atom2))
						new_monitor = formula_tree.new_monitor(formula_structure.get_formula_instance())
						static_qd_to_monitors[static_qd_index].append(new_monitor)

						add_timing_point("instantiated another monitor for static qd index %i" % static_qd_index)

						sub_verdict = new_monitor.process_atom_and_value(associated_atom, observed_value)
						if sub_verdict == True or sub_verdict == False:

							# record the monitor state with the binding
							if static_bindings_to_monitor_states.get(static_qd_index) is None:
								static_bindings_to_monitor_states[static_qd_index] = [new_monitor._state]
							elif not(new_monitor._state in static_bindings_to_monitor_states[static_qd_index]):
								static_bindings_to_monitor_states[static_qd_index].append(new_monitor._state)

							#pprint(static_bindings_to_monitor_states)

							# set the monitor to None
							static_qd_to_monitors[static_qd_index][-1] = None
							print("TRUE OR FALSE VERDICT REACHED")
							add_timing_point("verdict reached - monitor deleted")
							if check_monitor_size:
								add_monitor_size_point(static_qd_index, len(static_qd_to_monitors[static_qd_index])-1, 0, sub_verdict, "new")

							verdict_report.add_verdict(static_qd_index, sub_verdict)
						else:
							print("NO VERDICT REACHED")
							add_timing_point("processed observed value '%s' for atom %s" % (observed_value, associated_atom))
							#if check_monitor_size:
							#	add_monitor_size_point(static_qd_index, len(static_qd_to_monitors[static_qd_index])-1, len(new_monitor.get_unresolved_atoms()), sub_verdict, "new")

					else:
						# not the first bind variable
						# update existing monitors

						# this code is copy and pasted below - some refactoring needs to be done.

						for n in range(len(monitors)):
							# skip monitors that have reached verdicts
							if monitors[n] is None:
								continue

							print("updating monitor for static qd index %i" % static_qd_index)
							sub_verdict = monitors[n].process_atom_and_value(associated_atom, observed_value)
							if sub_verdict == True or sub_verdict == False:

								# record the monitor state with the binding
								if static_bindings_to_monitor_states.get(static_qd_index) is None:
									static_bindings_to_monitor_states[static_qd_index] = [monitors[n]._state]
								elif not(monitors[n]._state in static_bindings_to_monitor_states[static_qd_index]):
									static_bindings_to_monitor_states[static_qd_index].append(monitors[n]._state)

								#pprint(static_bindings_to_monitor_states)

								# set the monitor to None
								monitors[n] = None
								print("TRUE OR FALSE VERDICT REACHED")
								add_timing_point("verdict reached - monitor deleted")
								if check_monitor_size:
									add_monitor_size_point(static_qd_index, n, 0, sub_verdict, "existing")

								verdict_report.add_verdict(static_qd_index, sub_verdict)
							else:
								print("NO VERDICT REACHED")
								add_timing_point("processed observed value '%s' for atom %s" % (observed_value, associated_atom))
								if check_monitor_size:
									add_monitor_size_point(static_qd_index, n, len(monitors[n].get_unresolved_atoms()), sub_verdict, "existing")

						print("PROCESSING DONE FOR ATOM %s with value %s" % (associated_atom, observed_value))

						print("*****")
						print(static_bindings_to_monitor_states)
						print("*****")

			else:
				# this point can't trigger instantiation of a monitor for this element of the static qd
				# get all the monitors that are not None
				monitors = static_qd_to_monitors.get(static_qd_index)
				if monitors is None:
					# all previous monitors have been evaluated
					pass
				else:
					# update all the monitors
					for n in range(len(monitors)):
						# skip monitors that have reached verdicts
						if monitors[n] is None:
							continue

						print("updating monitor for static qd index %i" % static_qd_index)
						sub_verdict = monitors[n].process_atom_and_value(associated_atom, observed_value)
						if sub_verdict == True or sub_verdict == False:

							# record the monitor state with the binding
							if static_bindings_to_monitor_states.get(static_qd_index) is None:
								static_bindings_to_monitor_states[static_qd_index] = [monitors[n]._state]
							else:
								static_bindings_to_monitor_states[static_qd_index].append(monitors[n]._state)

							pprint(static_bindings_to_monitor_states)

							# set the monitor to None
							monitors[n] = None
							print("TRUE OR FALSE VERDICT REACHED")
							add_timing_point("verdict reached - monitor deleted")
							if check_monitor_size:
								add_monitor_size_point(static_qd_index, n, 0, sub_verdict, "existing")

							verdict_report.add_verdict(static_qd_index, sub_verdict)
						else:
							print("NO VERDICT REACHED")
							add_timing_point("processed observed value '%s' for atom %s" % (observed_value, associated_atom))
							if check_monitor_size:
								add_monitor_size_point(static_qd_index, n, len(monitors[n].get_unresolved_atoms()), sub_verdict, "existing")

			# set the task as done
			queue.task_done()

			print("CONSUMPTION DONE")

			print("="*100)

			if args.generate_vis_data:
				# update the time series
				if type(instrumentation_point) is CFGVertex:
					line_number = instrumentation_point._previous_edge._instruction.lineno
				else:
					line_number = instrumentation_point._instruction.lineno

				all_monitor_strings = []
				for monitor_list in static_qd_to_monitors.values():
					if monitor_list:
						all_monitor_strings += map(str, monitor_list)
				map_dump = json.dumps(all_monitor_strings)

				monitor_time_series.append((datetime.datetime.now(), line_number, map_dump))

	# setup the consumption queue for the monitor to read from
	queue = Queue.Queue()

	print("="*100)
	print("SETTING UP AND RUNNING PROGRAM + MONITORING THREAD")
	print("="*100)

	# create a new thread for the instrumented program
	new_code_obj = compile(ast_obj, filename="<ast>", mode="exec")
	program_thread = threading.Thread(target=program_thread_f, args=[new_code_obj])

	consumer_thread = threading.Thread(target=consumer_thread_f)

	add_timing_point("starting execution")

	# set up the verdict report
	verdict_report = VerdictReport()

	program_thread.start()
	consumer_thread.start()

	program_thread.join()
	consumer_thread.join()

	# change times for timing points
	for n in range(len(timing_points)):
		delta = timing_points[n]["timestamp"] - program_start_time
		timing_points[n]["timestamp"] = delta.total_seconds()

	# change times for monitor sizes
	for n in range(len(monitor_sizes)):
		delta = monitor_sizes[n]["timestamp"] - program_start_time
		monitor_sizes[n]["timestamp"] = delta.total_seconds()

	# write the timing information to the runs database
	connection = sqlite3.connect(db)
	cursor = connection.cursor()

	time_of_run = datetime.datetime.now()
	run_data = timing_points
	monitor_data = monitor_sizes

	cursor.execute("insert into run (time_of_run, run_data, monitor_data, optimised_monitor) values(?, ?, ?, ?)",
		[time_of_run, json.dumps(run_data), json.dumps(monitor_data), str(optimised_monitor)])
	connection.commit()
	connection.close()

	print("Program finished, and timing/monitor size data inserted into '%s'." % db)

	#pprint(monitor_sizes)

	# output verdict report

	print("-"*50)

	print("VERDICT REPORT")

	print("-"*50)
	
	report_map = verdict_report.get_final_verdict_report()

	for bind_space_index in report_map.keys():

		print("Binding")
		binding = bindings[bind_space_index]

		print("[")

		# for each element of the binding, print the appropriate representation
		for bind_var in binding:

			if type(bind_var) is CFGVertex:
				print("state change resulting from assignment to %s : line %i" %\
					(bind_var._previous_edge._instruction.targets[0].id, bind_var._previous_edge._instruction.lineno))
			elif type(bind_var) is CFGEdge:
				print("edge corresponding to call to %s : line %i" %\
					(bind_var._instruction.value.func.id, bind_var._instruction.lineno))

		print("]")

		print("gave verdicts %s" % (", ".join(map(str, report_map[bind_space_index]))))

		print("")


	# now, if the visualiser option has been given, output graphs for each stage of instrumentation
	if args.generate_vis_data:
		# output a graph for each binding
		for n in range(len(bindings)):
			print("binding", bindings[n])
			implicit_colourings = []
			for bind_variable_index in static_qd_to_point_map[n].keys():
				for (atom_index, point_atom_pair) in enumerate(static_qd_to_point_map[n][bind_variable_index]):
					points = point_atom_pair[0]
					atom = point_atom_pair[1]
					implicit_colourings += points

			print("implicit", implicit_colourings)

			output_file = args.graph[0].replace(".gv", "") + ("-%i" % n) + ".gv"
			graph = Digraph()
			graph.attr("graph", splines="true", fontsize="10")
			shape = "circle"
			for vertex in new_scfg.vertices:

				if vertex in bindings[n]:
					colour = "red"
				elif vertex in implicit_colourings:
					colour = "blue"
				else:
					colour = "white"

				graph.node(str(id(vertex)), vertex._name_changed, shape=shape, style="filled", fillcolor=colour)

				for edge in vertex.edges:

					if edge in bindings[n]:
						stroke = "red"
					elif edge in implicit_colourings:
						stroke = "blue"
					else:
						stroke = None

					graph.edge(
						str(id(vertex)),
						str(id(edge._target_state)),
						"%s : %s" % (str(edge._condition), instruction_to_string(edge._instruction)),
						color=stroke
					)
			graph.render(output_file)


		# write time series data
		ts_db = "run_descriptions.db"
		ts_con = sqlite3.connect(ts_db)
		ts_cursor = ts_con.cursor()
		for frame in monitor_time_series:
			ts_cursor.execute("insert into frame (frame_time, line_number, monitoring_map_dump) values (?, ?, ?)", frame)
		ts_con.commit()
		ts_con.close()