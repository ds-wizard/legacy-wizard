#!/bin/bash

gvim '+map <leader>r :!bin/reload.sh<cr>' '+:tabnew' '+:NERDTree app'
#'+:vertical resize 30<cr>'