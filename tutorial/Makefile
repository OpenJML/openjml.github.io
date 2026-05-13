# Gnu Makefile for the OpenJML tutorial
# This is used to create the .out files from the JML sources (typically .jml)

%.out: %.java
	-`sed -n -e '1s!// !!p' $<` >$@ 2>&1
