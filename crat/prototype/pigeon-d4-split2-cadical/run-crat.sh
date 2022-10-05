#!/bin/bash
for N in {3..10}
do
    make pst-crat N=$N
    make psd-crat N=$N
done

for N in {11..12}
do
    make pst-crat N=$N
done

