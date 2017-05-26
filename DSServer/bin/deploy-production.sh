#!/bin/bash

D="~/rsync/dmp.fairdata.solutions"

stack install DSServer
rsync -rvz --delete -e ssh bin static rob@ccmi.fit.cvut.cz:$D
rsync -rvz --delete -e ssh /home/rob/.local/bin/DSServer rob@ccmi.fit.cvut.cz:$D/dmp.fairdata.solutions

ssh -t rob@ccmi.fit.cvut.cz 'sudo chown -R www-data.www-data $D; sudo systemctl restart dmp.fairdata.solutions.service'
