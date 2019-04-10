"""
(C) Copyright 2018 CERN and University of Manchester.
This software is distributed under the terms of the GNU General Public Licence version 3 (GPL Version 3), copied verbatim in the file "COPYING".
In applying this licence, CERN does not waive the privileges and immunities granted to it by virtue of its status as an Intergovernmental Organization or submit itself to any jurisdiction.

Author: Joshua Dawes - CERN, University of Manchester - joshua.dawes@cern.ch
"""

def f(n):
	import time
	#print("f is executing - sleeping for %f seconds" % n)
	time.sleep(n)

x = 3
b = 60
for i in range(0, 500):
	a = 75+i
	for j in range(0, 5):
		if j < 3:
			z = 3
		else:
			z = 4
	f(cmd_params.delay)
	#print("end of iteration of loop")

y = 3
a = 50
i = 5
j = 5
if a < b:
	if i == j:
		for n in range(50):
			f(0.2)
		for n in range(50):
			f(0.1)
	c = 30
elif a < b + 10:
	d = 50
elif a < b + 20:
	f(3)
	e = 70
else:
	g = 20
	#print("TRAVERSING LAST BRANCH")
	f(2)
d = 30