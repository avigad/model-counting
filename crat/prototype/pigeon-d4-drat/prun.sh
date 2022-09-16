#!/bin/bash
for N in {3..9}
do
    make pst-all N=$N
    make psd-all N=$N
done

