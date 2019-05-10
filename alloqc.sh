#!/bin/bash

if [ -z $1 ]; then
  echo -e "Usage: alloqc.sh <filename>"
  exit 1
fi

OUTPUTNAME=$(basename "$1")
OUTPUTNAME="${OUTPUTNAME%.*}.v"

java -classpath .:./alloy4.2.jar Alloqc $1 > $OUTPUTNAME
