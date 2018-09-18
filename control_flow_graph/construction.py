from __future__ import print_function
def print(*args, **kwards):
	pass
"""
(C) Copyright 2018 CERN and University of Manchester.
This software is distributed under the terms of the GNU General Public Licence version 3 (GPL Version 3), copied verbatim in the file "COPYING".
In applying this licence, CERN does not waive the privileges and immunities granted to it by virtue of its status as an Intergovernmental Organization or submit itself to any jurisdiction.

Author: Joshua Dawes - CERN, University of Manchester - joshua.dawes@cern.ch
"""
"""

This module contains logic for construction of a specialised control flow graph.

"""

import ast
import os
import sys
import argparse
import traceback
from StringIO import StringIO
import datetime
import time
import threading
import Queue

from graphviz import Digraph
sys.path.append(".")
from monitor_synthesis import formula_tree
from formula_building.formula_building import *

vertices = []

"""def get_call_name_string_reversed(obj):
	Given an ast.Call object in call, recursively find the string representing the function called.
	If the call is simply a function, then this is straightforward.
	If the call is to a method, resolving it is slightly trickier.

	if type(obj) is ast.Str:
		return [obj.s]
	if type(obj) is ast.Name:
		return [obj.id]
	elif type(obj) is ast.Attribute:
		return [obj.attr] + get_call_name_string_reversed(obj.value)
	elif type(obj) is ast.Call:
		if type(obj.func) is ast.Attribute:
			return [obj.func.attr] + get_call_name_string_reversed(obj.func.value)
		elif type(obj.func) is ast.Subscript:
			return get_call_name_string_reversed(obj.func.value)
		elif type(obj.func) is ast.Name:
			return get_call_name_string_reversed(obj.func)

def get_call_name_string(obj):
	#print(obj.func)
	return ".".join(get_call_name_string_reversed(obj)[::-1])"""

def get_call_name_strings(obj):
	chain = list(ast.walk(obj))
	all_calls = filter(lambda item : type(item) is ast.Call, chain)
	full_names = {}
	for call in all_calls:
	    # construct the full function name for this call
	    current_item = call
	    full_names[call] = []
	    while not(type(current_item) is str):
	            if type(current_item) is ast.Call:
	                    current_item = current_item.func
	            elif type(current_item) is ast.Attribute:
	                    full_names[call].append(current_item.attr)
	                    current_item = current_item.value
	            elif type(current_item) is ast.Name:
	                    full_names[call].append(current_item.id)
	                    current_item = current_item.id
	return map(lambda item : ".".join(reversed(item)), full_names.values())

def get_attribute_string_reversed(obj):
	"""
	Given an ast.Attribute object, recursively find the string representing the attribute.
	Basically a simpler case of resolving call strings - the code could maybe be merged at some point.
	"""
	if type(obj) is ast.Name:
		return [obj.id]
	elif type(obj) is ast.Attribute:
		return [obj.attr] + get_attribute_string_reversed(obj.value)
	elif type(obj) is ast.Subscript:
		return get_attribute_string_reversed(obj.value)

def get_attr_name_string(obj):
	return ".".join(get_attribute_string_reversed(obj)[::-1])

class CFGVertex(object):
	"""
	This class represents a vertex in a control flow graph.
	Vertices correspond to states - a new state is induced when the value to which
	a name is mapped in Python code is changed.
	"""

	def __init__(self, entry=None):
		"""
		Given the name changed in the state this vertex represents,
		store it.
		Vertices can also have multiple edges leading out of them into next states.
		"""
		if not(entry):
			self._name_changed = []
		else:
			if type(entry) is ast.Assign and type(entry.value) is ast.Call:
				# only works for a single function being called - should make this recursive
				# for complex expressions that require multiple calls
				self._name_changed = [get_attr_name_string(entry.targets[0])] + get_call_name_strings(entry)
			elif type(entry) is ast.Expr and type(entry.value) is ast.Call:
				self._name_changed = get_call_name_strings(entry.value)
			elif type(entry) is ast.Assign:
				self._name_changed = [get_attr_name_string(entry.targets[0])]
			elif type(entry) is ast.Return:
				if type(entry.value) is ast.Call:
					self._name_changed = get_call_name_strings(entry.value)
				else:
					# nothing else could be changed
					self._name_changed = []
			elif type(entry) is ast.Raise:
				self._name_changed = [entry.type.func.id]
			elif type(entry) is ast.Print:
				self._name_changed = ["print"]

		self.edges = []
		self._previous_edge = None

	def add_outgoing_edge(self, edge):
		edge._source_state = self
		self.edges.append(edge)

	def __repr__(self):
		#return "%s=> %s" % (self._name_changed, self.edges)
		#return "<Vertex changing names %s %i on line %i>" % (self._name_changed, id(self._name_changed), self._previous_edge._instruction.lineno)
		return "<Vertex changing names %s %i>" % (self._name_changed, id(self._name_changed))

class CFGEdge(object):
	"""
	This class represents an edge in a control flow graph.
	"""

	def __init__(self, condition, instruction=None):
		self._condition = condition
		self._instruction = instruction
		self._source_state = None
		self._target_state = None

		if type(self._instruction) is ast.Assign and type(self._instruction.value) in [ast.Call, ast.Expr]:
			# we will have to deal with other kinds of expressions at some point
			self._operates_on = [get_attr_name_string(self._instruction.targets[0])] + get_call_name_strings(self._instruction.value)
		elif type(self._instruction) is ast.Assign and not(type(self._instruction.value) is ast.Call):
				self._operates_on = get_attr_name_string(self._instruction.targets[0])
		elif type(self._instruction) is ast.Expr and hasattr(self._instruction.value, "func"):
			self._operates_on = get_call_name_strings(self._instruction.value)
		elif type(self._instruction) is ast.Return and type(self._instruction.value) is ast.Call:
			self._operates_on = get_call_name_strings(self._instruction.value)
		elif type(self._instruction) is ast.Raise:
			self._operates_on = [self._instruction.type.func.id]
		else:
			self._operates_on = [self._instruction]

	def set_target_state(self, state):
		self._target_state = state
		if not(type(self._instruction) is str):
			state._previous_edge = self

	def __repr__(self):
		return "<Edge with instruction %s>" % self._instruction

class CFG(object):
	"""
	This class represents a symbolic control flow graph.
	"""

	def __init__(self):
		self.vertices = []
		self.edges = []
		empty_vertex = CFGVertex()
		self.vertices.append(empty_vertex)
		self.starting_vertices = empty_vertex
		self.return_statements = []

	def process_block(self, block, starting_vertices=None, condition=[]):
		"""
		Given a block, a set of starting vertices and to put on the first edge,
		construct the section of the control flow graph corresponding to this block.
		"""
		current_vertices = starting_vertices if not(starting_vertices is None) else [self.starting_vertices]

		print("starting vertices %s" % starting_vertices)

		print("processing block", block)

		for (n, entry) in enumerate(block):
			if type(entry) is ast.Assign or (type(entry) is ast.Expr and type(entry.value) is ast.Call):

				condition_to_use = condition if n == 0 else []

				# for each vertex in current_vertices, add an edge
				new_edges = []
				for vertex in current_vertices:
					entry._parent_body = block
					new_edge = CFGEdge(condition_to_use, entry)
					new_edges.append(new_edge)
					vertex.add_outgoing_edge(new_edge)

				# create a new vertex for the state created here
				new_vertex = CFGVertex(entry)

				self.vertices.append(new_vertex)
				self.edges += new_edges

				# direct all new edges to this new vertex
				for edge in new_edges:
					edge.set_target_state(new_vertex)

				# update current vertices
				current_vertices = [new_vertex]

				# filter out vertices that were returns or raises
				current_vertices = filter(lambda vertex : not(type(vertex._previous_edge._instruction) in [ast.Return, ast.Raise]), current_vertices)

			elif type(entry) is ast.Return:

				condition_to_use = condition if n == 0 else []

				new_edges = []
				for vertex in current_vertices:
					entry._parent_body = block
					new_edge = CFGEdge(condition_to_use, entry)
					new_edges.append(new_edge)
					vertex.add_outgoing_edge(new_edge)

				new_vertex = CFGVertex(entry)

				self.vertices.append(new_vertex)
				self.edges += new_edges

				# direct all new edges to this new vertex
				for edge in new_edges:
					edge.set_target_state(new_vertex)

				# update current vertices
				current_vertices = [new_vertex]

				self.return_statements.append(new_vertex)

				print("return statements are %s" % self.return_statements)

			elif type(entry) is ast.Raise:

				condition_to_use = condition if n == 0 else []

				new_edges = []
				for vertex in current_vertices:
					entry._parent_body = block
					new_edge = CFGEdge(condition_to_use, entry)
					new_edges.append(new_edge)
					vertex.add_outgoing_edge(new_edge)

				new_vertex = CFGVertex(entry)

				self.vertices.append(new_vertex)
				self.edges += new_edges

				# direct all new edges to this new vertex
				for edge in new_edges:
					edge.set_target_state(new_vertex)

				# update current vertices
				current_vertices = [new_vertex]

			elif type(entry) is ast.Print:

				condition_to_use = condition if n == 0 else []

				new_edges = []
				for vertex in current_vertices:
					entry._parent_body = block
					new_edge = CFGEdge(condition_to_use, entry)
					new_edges.append(new_edge)
					vertex.add_outgoing_edge(new_edge)

				new_vertex = CFGVertex(entry)

				self.vertices.append(new_vertex)
				self.edges += new_edges

				# direct all new edges to this new vertex
				for edge in new_edges:
					edge.set_target_state(new_vertex)

				# update current vertices
				current_vertices = [new_vertex]

			elif type(entry) is ast.If:
				# if we just have an if without an else block, this misses out the edge going from the state
				# before the conditional to the state after it (if the condition is false)
				# compute a list of pairs (condition, block) derived from the conditional
				pairs = [([entry.test], entry.body)]

				# need to accumulate conditions at some point

				#print(entry.orelse[0].orelse[0].__dict__)

				current_condition_set = [formula_tree.lnot(entry.test)]

				current_conditional = [entry]
				final_else_is_present = False
				# won't work when there is something after the second if in the else clause
				while type(current_conditional[0]) is ast.If:
					current_conditional = current_conditional[0].orelse
					if len(current_conditional) > 0:
						if type(current_conditional[0]) is ast.If:
							pairs.append((current_condition_set + [current_conditional[0].test], current_conditional[0].body))
							current_condition_set.append(formula_tree.lnot(current_conditional[0].test))
						else:
							pairs.append((current_condition_set, current_conditional))
							final_else_is_present = True
					else:
						# nowhere else to go in the traversal
						break

				print(pairs)

				# add the branches to the graph
				final_conditional_vertices = []
				for pair in pairs:
					final_vertices = self.process_block(pair[1], current_vertices, pair[0])
					final_conditional_vertices += final_vertices
					#vertices += final_vertices

				# we include the vertex before the conditional, only if there was no else
				if not(final_else_is_present):
					current_vertices = final_conditional_vertices + current_vertices
				else:
					current_vertices = final_conditional_vertices

				# filter out vertices that were returns or raises
				current_vertices = filter(lambda vertex : not(type(vertex._previous_edge._instruction) in [ast.Return, ast.Raise]), current_vertices)

				# add an empty "control flow" vertex after the conditional
				# to avoid transition duplication along the edges leaving
				# the conditional

				empty_vertex = CFGVertex()
				self.vertices.append(empty_vertex)
				for vertex in current_vertices:
					# an empty edge
					new_edge = CFGEdge("post-condition", "control-flow")
					self.edges.append(new_edge)
					new_edge.set_target_state(empty_vertex)
					vertex.add_outgoing_edge(new_edge)

				current_vertices = [empty_vertex]

			elif type(entry) is ast.TryExcept:

				blocks = [entry.body]

				for except_handler in entry.handlers:
					blocks.append(except_handler.body)

				final_try_catch_vertices = []
				for block_item in blocks:
					final_vertices = self.process_block(block_item, current_vertices, ['try-catch'])
					final_try_catch_vertices += final_vertices

				current_vertices = final_try_catch_vertices

				# filter out vertices that were returns or raises
				current_vertices = filter(lambda vertex : not(type(vertex._previous_edge._instruction) in [ast.Return, ast.Raise]), current_vertices)

			elif type(entry) is ast.For:

				# this will eventually be modified to include the loop variable as the state changed

				empty_pre_loop_vertex = CFGVertex()
				empty_post_loop_vertex = CFGVertex()
				self.vertices.append(empty_pre_loop_vertex)
				self.vertices.append(empty_post_loop_vertex)

				# link current_vertices to the pre-loop vertex
				for vertex in current_vertices:
					new_edge = CFGEdge("pre-loop", "control-flow")
					self.edges.append(new_edge)
					vertex.add_outgoing_edge(new_edge)
					new_edge.set_target_state(empty_pre_loop_vertex)

				current_vertices = [empty_pre_loop_vertex]

				# process loop body
				final_vertices = self.process_block(entry.body, current_vertices, ['for'])

				print("final vertex in loop", current_vertices[0].edges[0]._target_state)

				# add 2 edges from the final_vertex - one going back to the pre-loop vertex
				# with the positive condition, and one going to the post loop vertex.

				for final_vertex in final_vertices:
					for base_vertex in current_vertices:
						new_positive_edge = CFGEdge('loop-jump', 'loop-jump')
						self.edges.append(new_positive_edge)
						final_vertex.add_outgoing_edge(new_positive_edge)
						new_positive_edge.set_target_state(base_vertex)

						new_post_edge = CFGEdge("post-loop")
						self.edges.append(new_post_edge)
						final_vertex.add_outgoing_edge(new_post_edge)
						new_post_edge.set_target_state(empty_post_loop_vertex)

				current_vertices = [empty_post_loop_vertex]

			elif type(entry) is ast.While:

				final_vertices = self.process_block(entry.body, current_vertices, ['while'])

				print("final vertex in loop", current_vertices[0].edges[0]._target_state)

				for final_vertex in final_vertices:
					for base_vertex in current_vertices:
						new_positive_edge = CFGEdge('for', 'loop-jump')
						self.edges.append(new_positive_edge)
						final_vertex.add_outgoing_edge(new_positive_edge)
						new_positive_edge.set_target_state(base_vertex)

				current_vertices = final_vertices


		print("finished processing block")

		return current_vertices

	def next_calls(self, vertex, function, calls=[], marked_vertices=[]):
		"""
		Given a point (vertex or edge), find the set of next edges that model calls to function.
		"""
		print("marked vertices are %s" % marked_vertices)
		if not(vertex in marked_vertices):
			print("vertex %s not visited" % vertex)
			marked_vertices.append(vertex)
			edges = vertex.edges
			for edge in edges:
				if ((type(edge._instruction) is ast.Expr
					and hasattr(edge._instruction.value, "func")
					and function in get_call_name_strings(edge._instruction.value))
					or
					(type(edge._instruction) is ast.Assign
					and type(edge._instruction.value) is ast.Call and function in get_call_name_strings(edge._instruction.value))):
					print("edge calling %s is counted" % get_call_name_strings(edge._instruction.value))
					calls.append(edge)
				else:
					# this edge is not what we're looking for
					# so traverse this branch further
					print("recursing on vertex that changes %s" % edge._target_state._name_changed)
					self.next_calls(edge._target_state, function, calls, marked_vertices)
		else:
			print("vertex %s already visited" % vertex)

def expression_as_string(expression):
	if type(expression) is ast.Num:
		return str(expression.n)
	else:
		return str(expression)

def instruction_to_string(instruction):
	if type(instruction) is ast.Assign:
		return "%s = %s" % (get_attr_name_string(instruction.targets[0]), expression_as_string(instruction.value))
	elif type(instruction) is ast.Expr:
		return "%s()" % get_call_name_strings(instruction.value)