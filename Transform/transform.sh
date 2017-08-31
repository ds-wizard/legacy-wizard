#!/bin/bash
NEW_DSKM=`stack exec Transform $1`

echo "{-# LANGUAGE OverloadedStrings #-}" > dist/Questionnaire.hs
sed '/^formItems = .*$/d' src/Questionnaire.template.hs >> dist/Questionnaire.hs
echo "formItems = prepareForm $NEW_DSKM" >> dist/Questionnaire.hs
