#!/bin/bash
NEW_DSKM=$(./Transform/Main $1)

rm -f Transform/Questionnaire.hs
sed '/^formItems = .*$/d' Transform/Questionnaire.template.hs > Transform/Questionnaire.hs
echo "formItems = prepareForm $NEW_DSKM" >> Transform/Questionnaire.hs
