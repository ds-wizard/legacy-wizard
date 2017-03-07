#!/bin/bash

S="dmp.fairdata.solutions-testing"
D="/home/rob/rsync/$S"

stack install DSServer
rsync -rvz --delete -e ssh bin static rob@ccmi.fit.cvut.cz:$D
rsync -rvz --delete -e ssh /home/rob/.local/bin/DSServer rob@ccmi.fit.cvut.cz:$D/$S

ssh -t rob@ccmi.fit.cvut.cz "sudo systemctl restart $S.service"
