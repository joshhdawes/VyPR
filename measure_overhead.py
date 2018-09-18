"""
Python script to run VyPR a number of times determined by the input both with and without monitoring.
"""

from subprocess import call
from datetime import datetime
import argparse

if __name__ == "__main__":
	parser = argparse.ArgumentParser(description='Run VyPR a given number of times with and without monitoring to measure the overhead.')
	parser.add_argument('--program', type=str, nargs=1, help='The filename in which the program to instrument and run is found.', required=True)
	parser.add_argument('--property', type=str, nargs=1, help='The filename in which the property to check is found.', required=True)
	parser.add_argument('--runs', type=int, nargs=1, help='The number of times to run VyPR with and without monitoring turned on.', required=True)

	args = parser.parse_args()

	command_with_monitoring = "python verification.py --program %s --optimised-monitor --db runs.db --property %s --verify" % (args.program[0], args.property[0])
	command_without_monitoring = "python verification.py --program %s --optimised-monitor --db runs.db --property %s" % (args.program[0], args.property[0])

	monitored_times = []
	unmonitored_times = []

	for n in range(args.runs[0]):
		start = datetime.now()
		call(command_with_monitoring.split(" "))
		end = datetime.now()
		duration = (end-start).total_seconds()
		monitored_times.append(duration)

		start = datetime.now()
		call(command_without_monitoring.split(" "))
		end = datetime.now()
		duration = (end-start).total_seconds()
		unmonitored_times.append(duration)

	percentage_extras = map(lambda pair : ((pair[1] - pair[0])/pair[0])*100, zip(unmonitored_times, monitored_times))
	average = sum(percentage_extras) / float(len(percentage_extras))

	print("Average overhead across %i runs was %f%%" % (args.runs[0], average))