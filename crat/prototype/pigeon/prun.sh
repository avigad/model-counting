#!/bin/bash
for N in {3..8}
do
    make psd-all N=$N
    make pst-all N=$N
done

