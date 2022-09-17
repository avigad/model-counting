#!/bin/bash
for N in {3..10}
do
    make pst-all N=$N
    make psd-all N=$N
done

