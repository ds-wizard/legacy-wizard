#!/bin/bash
NEW_DSKM=$(dist/build/Transform/Transform $1)

rm -f Questionnaire.hs
echo "{-# LANGUAGE OverloadedStrings #-}" > dist/Questionnaire.hs
sed '/^formItems = .*$/d' src/Questionnaire.template.hs >> dist/Questionnaire.hs
echo "formItems = prepareForm $NEW_DSKM" >> dist/Questionnaire.hs
