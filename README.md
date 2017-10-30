# Malloclab (Memorylab)

> Copyright (c) 2002, R. Bryant and D. O'Hallaron, All rights reserved. May not be used, modified, or copied without permission.

## Main Files:

* `mm.{c,h}`: Your solution malloc package. mm.c is the file that you will be handing in, and is the only file you should modify.

* `mdriver.c`: The malloc driver that tests your mm.c file

* `traces/*.rep`: Trace files

* `Makefile`: Builds the driver

## Other support files for the driver

* ` config.h`: Configures the malloc lab driver

* `fsecs.{c,h}`: Wrapper function for the different timer packages

* `clock.{c,h}`: Routines for accessing the Pentium and Alpha cycle counters

* `fcyc.{c,h}`: Timer functions based on cycle counters

* `ftimer.{c,h}`: Timer functions based on interval timers and gettimeofday()

* `memlib.{c,h}`: Models the heap and sbrk function

## Building and running the driver

* To build the driver, type "make" to the shell.

* To run the driver on a tiny test trace:

    `devel@getnoo ~/malloclab $ mdriver -V -f traces/short1-bal.rep`

* The `-V` option prints out helpful tracing and summary information.

* To get a list of the driver flags:

    `devel@getnoo ~/malloclab $ mdriver -h`
