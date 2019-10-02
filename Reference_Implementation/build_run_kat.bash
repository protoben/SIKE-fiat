#!/bin/bash

mkdir -p build
cd build
cmake ..
make

if [ "$1" == "p434" ]
then
    cd SIKEp434
    ./kat_SIKEp434
elif [ "$1" == "p503" ]
then
    cd SIKEp503
    ./kat_SIKEp503
elif [ "$1" == "p610" ]
then
    cd SIKEp610
    ./kat_SIKEp610
elif [ "$1" == "p751" ]
then
    cd SIKEp751
    ./kat_SIKEp751
fi
