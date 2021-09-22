#!/bin/sh

EXEEXT=
srcdir=.

PIP_TESTS="\
	phideo.pip \
	seghir-e1.pip \
	seghir-e3.pip \
	seghir-e4.pip \
	seghir-e5.pip \
	seghir-e6.pip \
	seghir-e7.pip \
	seghir-e8.pip \
	seghir-e9.pip \
	seghir-vd.pip \
	bouleti.pip \
	difficult.pip \
	cnt_sum2.pip \
	jcomplex.pip"

for i in $PIP_TESTS; do
	echo $i;
	./isl_pip$EXEEXT --format=set --context=gbr -T < $srcdir/testsets/pip/$i || exit
	./isl_pip$EXEEXT --format=set --context=lexmin -T < $srcdir/testsets/pip/$i || exit
	./isl_pip$EXEEXT --format=affine --context=gbr -T < $srcdir/testsets/pip/$i || exit
	./isl_pip$EXEEXT --format=affine --context=lexmin -T < $srcdir/testsets/pip/$i || exit
done
