"""
(C) Copyright 2018 CERN and University of Manchester.
This software is distributed under the terms of the GNU General Public Licence version 3 (GPL Version 3), copied verbatim in the file "COPYING".
In applying this licence, CERN does not waive the privileges and immunities granted to it by virtue of its status as an Intergovernmental Organization or submit itself to any jurisdiction.

Author: Joshua Dawes - CERN, University of Manchester - joshua.dawes@cern.ch
"""

formula_structure = Forall(
		StaticState('q', 'a')
	).Forall(
		StaticTransition('t', 'f', uses='q')
	).Formula(
		lambda q, t: (
			If(
				q('a')._in([0, 80])
			).then(
				t.duration()._in([0, 1])
			)
		)
	)