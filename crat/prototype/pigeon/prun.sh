#!/bin/bash

for N in {3..9}
do
    make psd-all N=$N
    make pst-all N=$N
done

