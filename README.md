# Prototype of the VyPR Runtime Verification tool

The tool in this repository is for verification of input Python (2.7) programs with respect to specifications written in our new logic, Control Flow Temporal Logic.

(C) Copyright 2018 CERN and University of Manchester.
This software is distributed under the terms of the GNU General Public Licence version 3 (GPL Version 3), copied verbatim in the file "COPYING".
In applying this licence, CERN does not waive the privileges and immunities granted to it by virtue of its status as an Intergovernmental Organization or submit itself to any jurisdiction.

Author: Joshua Dawes - CERN, University of Manchester

**VyPR is beginning a period of extensive development, which will include writing much more thorough (and up to date) documentation.  To use VyPR, follow the instructions at http://cern.ch/vypr/use-vypr.html.**

## Setup

To use VyPR, setup a virtual environment for Python in the directory in which you will run the tool.

Virtual environments are a way to sandbox code, and prevent installing libraries that a single project needs for the entire system.

This can be done by first installing `virtualenv` with `pip`, then running `virtualenv venv`.  This will setup a directory called `venv` in that subdirectory with all necessary Python-related libraries.  You can then run `source ./venv/bin/activate` to initialise the virtual environment.

Once the virtual environment is initialised, run `pip install -r requirements.txt` from inside the tool directory to install the Python dependencies *inside the virtual environment* (if you do this outside of the virtual environment, you will install the dependencies globally).

## Verification

Running `python verification.py -h` will output the following:

```
usage: verification.py [-h] --program PROGRAM [--graph GRAPH]
                       [--optimised-monitor] [--verify] --db DB --property
                       PROPERTY [--check-monitor]

Read in a sample program, instrument it for a property, and run it with
monitoring.

optional arguments:
  -h, --help           show this help message and exit
  --program PROGRAM    The filename in which the program to instrument and run
                       is found.
  --graph GRAPH        The filename of the graph to output.
  --optimised-monitor  If supplied, use optimised monitor update.
  --verify             If supplied, apply verification.
  --db DB              The database to write the log to - we use this for
                       performance analysis of the monitoring.
  --property PROPERTY  The file in which the property definition is found for
                       verification.
  --check-monitor      If supplied, the monitor size will be tracked.
```

The command line options are as follows:

* `--program` indicates the file name in which the program to be verified is found.
* `--graph` indicates the file name to which the Symbolic Control Flow graph derived from the input program is written.  The format used is graphviz (.gv); when running on my machine, a pdf of the compiled gv file is also generated.
* `--optimised-monitor` tells the verification tool to use an optimisation when changing monitor states during verification.
* `--verify` tells the verification tool to actually verify the program.  Omitting this option will run the input program normally.
* `--db` indicates the database file name to use when storing data about the verification process.  This is normally an SQLite database file which one can setup for use by the verification tool using `CREATE TABLE run ( time_of_run timestamp primary key, run_data text, monitor_data text, optimised_monitor text );` in an SQLite client.
* `--property` indicates the file name in which the Python code specifying the property is found.  See below for documentation about the property specification library.
* `--check-monitor`, if given, tells the verification tool to store information about monitor sizes over time in the run information in `--db`.

There are some sample properties in `test_properties/` and some sample programs in `test_programs/`.  If you'd like to use VyPR, let us know: http://cern.ch/vypr/use-vypr.html.
