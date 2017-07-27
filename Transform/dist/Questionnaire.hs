{-# LANGUAGE OverloadedStrings #-}

module Questionnaire
  ( formItems
  ) where

import FormEngine.FormItem

formItems :: [FormItem]
formItems =
  prepareForm
    [ Chapter
      { chDescriptor = defaultFIDescriptor {iLabel = Just "Basic information"}
      , chItems = [TextFI {tfiDescriptor = defaultFIDescriptor {iLabel = Just "Description of your case"}}]
      }
    , Chapter
      { chDescriptor =
          FIDescriptor
          { iLabel = Just "Design of the experiment"
          , iNumbering = NoNumbering
          , iIdent = Nothing
          , iTags = []
          , iShortDescription = Nothing
          , iLongDescription = Nothing
          , chapterId = Just 1
          , questionId = Nothing
          , iLink = Nothing
          , iMandatory = False
          , iRules = []
          , iAutoComplete = []
          }
      , chItems =
          [ InfoFI
            { ifiDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 1
                , questionId = Nothing
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , ifiText =
                "Before you decide to embark on any new study, it is nowadays good practice to consider all options to keep the data generation part of your study as limited as possible. It is not because we can generate massive amounts of data that we always need to do so. Creating data with public money is bringing with it the responsibility to treat those data well and (if potentially useful) make them available for re-use by others."
            }
          , SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 1
                , questionId = Just 1
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "Is there any pre-existing data?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription =
                          Just
                            "<p class=\"question-description\">Are there any data sets available in the world that are relevant to your planned research?</p>"
                      , chapterId = Just 1
                      , questionId = Just 1
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions =
                      [ DetailedOption
                          NoNumbering
                          "No"
                          [ SimpleGroup
                            { sgDescriptor =
                                FIDescriptor
                                { iLabel = Nothing
                                , iNumbering = NoNumbering
                                , iIdent = Nothing
                                , iTags = []
                                , iShortDescription = Nothing
                                , iLongDescription = Nothing
                                , chapterId = Just 1
                                , questionId = Just 1
                                , iLink = Nothing
                                , iMandatory = True
                                , iRules = []
                                , iAutoComplete = []
                                }
                            , sgLevel = 0
                            , sgItems =
                                [ InfoFI
                                  { ifiDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 1
                                      , questionId = Just 1
                                      , iLink = Nothing
                                      , iMandatory = True
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , ifiText =
                                      "You know that this is very unlikely? This question is not only about data sets that are similar to what you want to determine yourself, but also reference data or data that should be mined from the existing literature. Further, it is very likely that you will refer to related data, e.g. other databases where you usually \"quickly look something up\", but that could maybe be properly integrated, especially if you need to do such lookups multiple times."
                                  }
                                ]
                            }
                          ]
                      , DetailedOption
                          NoNumbering
                          "Yes"
                          [ SimpleGroup
                            { sgDescriptor =
                                FIDescriptor
                                { iLabel = Nothing
                                , iNumbering = NoNumbering
                                , iIdent = Nothing
                                , iTags = []
                                , iShortDescription = Nothing
                                , iLongDescription = Nothing
                                , chapterId = Just 1
                                , questionId = Just 1
                                , iLink = Nothing
                                , iMandatory = True
                                , iRules = []
                                , iAutoComplete = []
                                }
                            , sgLevel = 0
                            , sgItems =
                                [ SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 1
                                      , questionId = Just 2
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel =
                                                Just
                                                  "Will you be using any pre-existing data (including other people's data)?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription =
                                                Just
                                                  "<p class=\"question-description\">Will you be referring to any earlier measured data, reference data, or data that should be mined from existing literature? Your own data as well as data from others?</p>"
                                            , chapterId = Just 1
                                            , questionId = Just 2
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions =
                                            [ DetailedOption
                                                NoNumbering
                                                "No"
                                                [ SimpleGroup
                                                  { sgDescriptor =
                                                      FIDescriptor
                                                      { iLabel = Nothing
                                                      , iNumbering = NoNumbering
                                                      , iIdent = Nothing
                                                      , iTags = []
                                                      , iShortDescription = Nothing
                                                      , iLongDescription = Nothing
                                                      , chapterId = Just 1
                                                      , questionId = Just 2
                                                      , iLink = Nothing
                                                      , iMandatory = True
                                                      , iRules = []
                                                      , iAutoComplete = []
                                                      }
                                                  , sgLevel = 0
                                                  , sgItems =
                                                      [ InfoFI
                                                        { ifiDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 1
                                                            , questionId = Just 2
                                                            , iLink = Nothing
                                                            , iMandatory = True
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , ifiText =
                                                            "Did you research all the data that exists? You may not be aware of all existing data that could be available. Although using and/or integrating existing data sets may pose a challenge, it will normally be cheaper than collecting everything yourself. Even if you decide not to use an existing data set, it is better to do this as a conscious decision."
                                                        }
                                                      ]
                                                  }
                                                ]
                                            , DetailedOption
                                                NoNumbering
                                                "Yes"
                                                [ SimpleGroup
                                                  { sgDescriptor =
                                                      FIDescriptor
                                                      { iLabel = Nothing
                                                      , iNumbering = NoNumbering
                                                      , iIdent = Nothing
                                                      , iTags = []
                                                      , iShortDescription = Nothing
                                                      , iLongDescription = Nothing
                                                      , chapterId = Just 1
                                                      , questionId = Just 2
                                                      , iLink = Nothing
                                                      , iMandatory = True
                                                      , iRules = []
                                                      , iAutoComplete = []
                                                      }
                                                  , sgLevel = 0
                                                  , sgItems =
                                                      [ SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 1
                                                            , questionId = Just 3
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ MultipleGroup
                                                              { mgDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel = Just "What reference data will you use?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription =
                                                                      Just "List all the items bellow."
                                                                  , iLongDescription =
                                                                      Just
                                                                        "<p class=\"question-description\">Much of todays data is used in comparison with reference data. A genome for instance is compared with a reference genome to identify genomic variants. If you use reference data, there are several other issues that you should consider. What are the reference data sets that you will use?</p>"
                                                                  , chapterId = Just 1
                                                                  , questionId = Just 3
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , mgLevel = 0
                                                              , mgItems =
                                                                  [ StringFI
                                                                    { sfiDescriptor =
                                                                        FIDescriptor
                                                                        { iLabel = Just "Item"
                                                                        , iNumbering = NoNumbering
                                                                        , iIdent = Nothing
                                                                        , iTags = []
                                                                        , iShortDescription = Nothing
                                                                        , iLongDescription =
                                                                            Just
                                                                              "<p class=\"question-description\">Much of todays data is used in comparison with reference data. A genome for instance is compared with a reference genome to identify genomic variants. If you use reference data, there are several other issues that you should consider. What are the reference data sets that you will use?</p>"
                                                                        , chapterId = Just 1
                                                                        , questionId = Just 3
                                                                        , iLink = Nothing
                                                                        , iMandatory = False
                                                                        , iRules = []
                                                                        , iAutoComplete = []
                                                                        }
                                                                    }
                                                                  , SimpleGroup
                                                                    { sgDescriptor =
                                                                        FIDescriptor
                                                                        { iLabel = Nothing
                                                                        , iNumbering = NoNumbering
                                                                        , iIdent = Nothing
                                                                        , iTags = []
                                                                        , iShortDescription = Nothing
                                                                        , iLongDescription = Nothing
                                                                        , chapterId = Just 1
                                                                        , questionId = Just 4
                                                                        , iLink = Nothing
                                                                        , iMandatory = False
                                                                        , iRules = []
                                                                        , iAutoComplete = []
                                                                        }
                                                                    , sgLevel = 0
                                                                    , sgItems =
                                                                        [ ChoiceFI
                                                                          { chfiDescriptor =
                                                                              FIDescriptor
                                                                              { iLabel =
                                                                                  Just
                                                                                    "Do you know where and how is it available?"
                                                                              , iNumbering = NoNumbering
                                                                              , iIdent = Nothing
                                                                              , iTags = []
                                                                              , iShortDescription = Nothing
                                                                              , iLongDescription =
                                                                                  Just
                                                                                    "<p class=\"question-description\">Do you know where the reference data is available, what the conditions for use are, and how to reference it?</p>"
                                                                              , chapterId = Just 1
                                                                              , questionId = Just 4
                                                                              , iLink = Nothing
                                                                              , iMandatory = True
                                                                              , iRules = []
                                                                              , iAutoComplete = []
                                                                              }
                                                                          , chfiAvailableOptions =
                                                                              [ DetailedOption
                                                                                  NoNumbering
                                                                                  "No"
                                                                                  [ SimpleGroup
                                                                                    { sgDescriptor =
                                                                                        FIDescriptor
                                                                                        { iLabel = Nothing
                                                                                        , iNumbering = NoNumbering
                                                                                        , iIdent = Nothing
                                                                                        , iTags = []
                                                                                        , iShortDescription = Nothing
                                                                                        , iLongDescription = Nothing
                                                                                        , chapterId = Just 1
                                                                                        , questionId = Just 4
                                                                                        , iLink = Nothing
                                                                                        , iMandatory = True
                                                                                        , iRules = []
                                                                                        , iAutoComplete = []
                                                                                        }
                                                                                    , sgLevel = 0
                                                                                    , sgItems =
                                                                                        [ InfoFI
                                                                                          { ifiDescriptor =
                                                                                              FIDescriptor
                                                                                              { iLabel = Nothing
                                                                                              , iNumbering = NoNumbering
                                                                                              , iIdent = Nothing
                                                                                              , iTags = []
                                                                                              , iShortDescription =
                                                                                                  Nothing
                                                                                              , iLongDescription =
                                                                                                  Nothing
                                                                                              , chapterId = Just 1
                                                                                              , questionId = Just 4
                                                                                              , iLink = Nothing
                                                                                              , iMandatory = True
                                                                                              , iRules = []
                                                                                              , iAutoComplete = []
                                                                                              }
                                                                                          , ifiText =
                                                                                              "Figure this out quickly!"
                                                                                          }
                                                                                        ]
                                                                                    }
                                                                                  ]
                                                                              , SimpleOption "Yes"
                                                                              ]
                                                                          }
                                                                        ]
                                                                    }
                                                                  , SimpleGroup
                                                                    { sgDescriptor =
                                                                        FIDescriptor
                                                                        { iLabel = Nothing
                                                                        , iNumbering = NoNumbering
                                                                        , iIdent = Nothing
                                                                        , iTags = []
                                                                        , iShortDescription = Nothing
                                                                        , iLongDescription = Nothing
                                                                        , chapterId = Just 1
                                                                        , questionId = Just 5
                                                                        , iLink = Nothing
                                                                        , iMandatory = False
                                                                        , iRules = []
                                                                        , iAutoComplete = []
                                                                        }
                                                                    , sgLevel = 0
                                                                    , sgItems =
                                                                        [ ChoiceFI
                                                                          { chfiDescriptor =
                                                                              FIDescriptor
                                                                              { iLabel =
                                                                                  Just
                                                                                    "Do you knpw in what format the reference data is available?"
                                                                              , iNumbering = NoNumbering
                                                                              , iIdent = Nothing
                                                                              , iTags = []
                                                                              , iShortDescription = Nothing
                                                                              , iLongDescription =
                                                                                  Just
                                                                                    "<p class=\"question-description\">Do you know the data format of the reference data? Is this suitable for your work? Does it need to be converted?</p>"
                                                                              , chapterId = Just 1
                                                                              , questionId = Just 5
                                                                              , iLink = Nothing
                                                                              , iMandatory = True
                                                                              , iRules = []
                                                                              , iAutoComplete = []
                                                                              }
                                                                          , chfiAvailableOptions =
                                                                              [ SimpleOption "I can directly use it"
                                                                              , SimpleOption
                                                                                  "I need to convert it before using"
                                                                              ]
                                                                          }
                                                                        ]
                                                                    }
                                                                  , SimpleGroup
                                                                    { sgDescriptor =
                                                                        FIDescriptor
                                                                        { iLabel = Nothing
                                                                        , iNumbering = NoNumbering
                                                                        , iIdent = Nothing
                                                                        , iTags = []
                                                                        , iShortDescription = Nothing
                                                                        , iLongDescription = Nothing
                                                                        , chapterId = Just 1
                                                                        , questionId = Just 6
                                                                        , iLink = Nothing
                                                                        , iMandatory = False
                                                                        , iRules = []
                                                                        , iAutoComplete = []
                                                                        }
                                                                    , sgLevel = 0
                                                                    , sgItems =
                                                                        [ ChoiceFI
                                                                          { chfiDescriptor =
                                                                              FIDescriptor
                                                                              { iLabel =
                                                                                  Just
                                                                                    "Is the reference data resource versioned?"
                                                                              , iNumbering = NoNumbering
                                                                              , iIdent = Nothing
                                                                              , iTags = []
                                                                              , iShortDescription = Nothing
                                                                              , iLongDescription =
                                                                                  Just
                                                                                    "<p class=\"question-description\">Many reference data sets evolve over time. If the reference data set changes, this may affect your results. If different versions of a reference data set exist, you need to establish your \"version policy\".</p>"
                                                                              , chapterId = Just 1
                                                                              , questionId = Just 6
                                                                              , iLink = Nothing
                                                                              , iMandatory = True
                                                                              , iRules = []
                                                                              , iAutoComplete = []
                                                                              }
                                                                          , chfiAvailableOptions =
                                                                              [ SimpleOption "No"
                                                                              , DetailedOption
                                                                                  NoNumbering
                                                                                  "Yes"
                                                                                  [ SimpleGroup
                                                                                    { sgDescriptor =
                                                                                        FIDescriptor
                                                                                        { iLabel = Nothing
                                                                                        , iNumbering = NoNumbering
                                                                                        , iIdent = Nothing
                                                                                        , iTags = []
                                                                                        , iShortDescription = Nothing
                                                                                        , iLongDescription = Nothing
                                                                                        , chapterId = Just 1
                                                                                        , questionId = Just 6
                                                                                        , iLink = Nothing
                                                                                        , iMandatory = True
                                                                                        , iRules = []
                                                                                        , iAutoComplete = []
                                                                                        }
                                                                                    , sgLevel = 0
                                                                                    , sgItems =
                                                                                        [ SimpleGroup
                                                                                          { sgDescriptor =
                                                                                              FIDescriptor
                                                                                              { iLabel = Nothing
                                                                                              , iNumbering = NoNumbering
                                                                                              , iIdent = Nothing
                                                                                              , iTags = []
                                                                                              , iShortDescription =
                                                                                                  Nothing
                                                                                              , iLongDescription =
                                                                                                  Nothing
                                                                                              , chapterId = Just 1
                                                                                              , questionId = Just 7
                                                                                              , iLink = Nothing
                                                                                              , iMandatory = False
                                                                                              , iRules = []
                                                                                              , iAutoComplete = []
                                                                                              }
                                                                                          , sgLevel = 0
                                                                                          , sgItems =
                                                                                              [ TextFI
                                                                                                { tfiDescriptor =
                                                                                                    FIDescriptor
                                                                                                    { iLabel =
                                                                                                        Just
                                                                                                          "Which version will you use?"
                                                                                                    , iNumbering =
                                                                                                        NoNumbering
                                                                                                    , iIdent = Nothing
                                                                                                    , iTags = []
                                                                                                    , iShortDescription =
                                                                                                        Nothing
                                                                                                    , iLongDescription =
                                                                                                        Just
                                                                                                          "If there are different versions available, you have to decide with all project partners together which version you will be using. Probably you will go for the latest release as of the date of the start of your research project. However, if you have other data from older projects that need to be merged, you may need to consider using the same release you used for a previous project."
                                                                                                    , chapterId = Just 1
                                                                                                    , questionId =
                                                                                                        Just 7
                                                                                                    , iLink = Nothing
                                                                                                    , iMandatory = True
                                                                                                    , iRules = []
                                                                                                    , iAutoComplete = []
                                                                                                    }
                                                                                                }
                                                                                              ]
                                                                                          }
                                                                                        , SimpleGroup
                                                                                          { sgDescriptor =
                                                                                              FIDescriptor
                                                                                              { iLabel = Nothing
                                                                                              , iNumbering = NoNumbering
                                                                                              , iIdent = Nothing
                                                                                              , iTags = []
                                                                                              , iShortDescription =
                                                                                                  Nothing
                                                                                              , iLongDescription =
                                                                                                  Nothing
                                                                                              , chapterId = Just 1
                                                                                              , questionId = Just 8
                                                                                              , iLink = Nothing
                                                                                              , iMandatory = False
                                                                                              , iRules = []
                                                                                              , iAutoComplete = []
                                                                                              }
                                                                                          , sgLevel = 0
                                                                                          , sgItems =
                                                                                              [ ChoiceFI
                                                                                                { chfiDescriptor =
                                                                                                    FIDescriptor
                                                                                                    { iLabel =
                                                                                                        Just
                                                                                                          "Will you change version if it updates?"
                                                                                                    , iNumbering =
                                                                                                        NoNumbering
                                                                                                    , iIdent = Nothing
                                                                                                    , iTags = []
                                                                                                    , iShortDescription =
                                                                                                        Nothing
                                                                                                    , iLongDescription =
                                                                                                        Just
                                                                                                          "<p class=\"question-description\">If the reference changes while you are working on your research project, you need to decide whether you will follow these changes. Most likely that will mean that you have to do some analyses again, so you will need to make sure enough resources are available to do so. You can decide to stay with the version that you started with; this can have the disadvantage that you will not benefit from added information or added consistency.</p>"
                                                                                                    , chapterId = Just 1
                                                                                                    , questionId =
                                                                                                        Just 8
                                                                                                    , iLink = Nothing
                                                                                                    , iMandatory = True
                                                                                                    , iRules = []
                                                                                                    , iAutoComplete = []
                                                                                                    }
                                                                                                , chfiAvailableOptions =
                                                                                                    [ DetailedOption
                                                                                                        NoNumbering
                                                                                                        "Will stay with the old version"
                                                                                                        [ SimpleGroup
                                                                                                          { sgDescriptor =
                                                                                                              FIDescriptor
                                                                                                              { iLabel =
                                                                                                                  Nothing
                                                                                                              , iNumbering =
                                                                                                                  NoNumbering
                                                                                                              , iIdent =
                                                                                                                  Nothing
                                                                                                              , iTags =
                                                                                                                  []
                                                                                                              , iShortDescription =
                                                                                                                  Nothing
                                                                                                              , iLongDescription =
                                                                                                                  Nothing
                                                                                                              , chapterId =
                                                                                                                  Just 1
                                                                                                              , questionId =
                                                                                                                  Just 8
                                                                                                              , iLink =
                                                                                                                  Nothing
                                                                                                              , iMandatory =
                                                                                                                  True
                                                                                                              , iRules =
                                                                                                                  []
                                                                                                              , iAutoComplete =
                                                                                                                  []
                                                                                                              }
                                                                                                          , sgLevel = 0
                                                                                                          , sgItems =
                                                                                                              [ SimpleGroup
                                                                                                                { sgDescriptor =
                                                                                                                    FIDescriptor
                                                                                                                    { iLabel =
                                                                                                                        Nothing
                                                                                                                    , iNumbering =
                                                                                                                        NoNumbering
                                                                                                                    , iIdent =
                                                                                                                        Nothing
                                                                                                                    , iTags =
                                                                                                                        [
                                                                                                                        ]
                                                                                                                    , iShortDescription =
                                                                                                                        Nothing
                                                                                                                    , iLongDescription =
                                                                                                                        Nothing
                                                                                                                    , chapterId =
                                                                                                                        Just
                                                                                                                          1
                                                                                                                    , questionId =
                                                                                                                        Just
                                                                                                                          79
                                                                                                                    , iLink =
                                                                                                                        Nothing
                                                                                                                    , iMandatory =
                                                                                                                        False
                                                                                                                    , iRules =
                                                                                                                        [
                                                                                                                        ]
                                                                                                                    , iAutoComplete =
                                                                                                                        [
                                                                                                                        ]
                                                                                                                    }
                                                                                                                , sgLevel =
                                                                                                                    0
                                                                                                                , sgItems =
                                                                                                                    [ ChoiceFI
                                                                                                                      { chfiDescriptor =
                                                                                                                          FIDescriptor
                                                                                                                          { iLabel =
                                                                                                                              Just
                                                                                                                                "How will the old version be available?"
                                                                                                                          , iNumbering =
                                                                                                                              NoNumbering
                                                                                                                          , iIdent =
                                                                                                                              Nothing
                                                                                                                          , iTags =
                                                                                                                              [
                                                                                                                              ]
                                                                                                                          , iShortDescription =
                                                                                                                              Nothing
                                                                                                                          , iLongDescription =
                                                                                                                              Just
                                                                                                                                "<p class=\"question-description\">Since you want to keep using the old version of the reference data, how will it be available to you?</p>"
                                                                                                                          , chapterId =
                                                                                                                              Just
                                                                                                                                1
                                                                                                                          , questionId =
                                                                                                                              Just
                                                                                                                                79
                                                                                                                          , iLink =
                                                                                                                              Nothing
                                                                                                                          , iMandatory =
                                                                                                                              True
                                                                                                                          , iRules =
                                                                                                                              [
                                                                                                                              ]
                                                                                                                          , iAutoComplete =
                                                                                                                              [
                                                                                                                              ]
                                                                                                                          }
                                                                                                                      , chfiAvailableOptions =
                                                                                                                          [ SimpleOption
                                                                                                                              "I will need it only at the beginning"
                                                                                                                          , SimpleOption
                                                                                                                              "I will use a downloaded version"
                                                                                                                          , SimpleOption
                                                                                                                              "The provider keeps old versions around"
                                                                                                                          ]
                                                                                                                      }
                                                                                                                    ]
                                                                                                                }
                                                                                                              ]
                                                                                                          }
                                                                                                        ]
                                                                                                    , SimpleOption
                                                                                                        "New analyses will be done with the new version"
                                                                                                    , SimpleOption
                                                                                                        "All analyses will be redone with the new version"
                                                                                                    ]
                                                                                                }
                                                                                              ]
                                                                                          }
                                                                                        ]
                                                                                    }
                                                                                  ]
                                                                              ]
                                                                          }
                                                                        ]
                                                                    }
                                                                  , SimpleGroup
                                                                    { sgDescriptor =
                                                                        FIDescriptor
                                                                        { iLabel = Nothing
                                                                        , iNumbering = NoNumbering
                                                                        , iIdent = Nothing
                                                                        , iTags = []
                                                                        , iShortDescription = Nothing
                                                                        , iLongDescription = Nothing
                                                                        , chapterId = Just 1
                                                                        , questionId = Just 80
                                                                        , iLink = Nothing
                                                                        , iMandatory = False
                                                                        , iRules = []
                                                                        , iAutoComplete = []
                                                                        }
                                                                    , sgLevel = 0
                                                                    , sgItems =
                                                                        [ ChoiceFI
                                                                          { chfiDescriptor =
                                                                              FIDescriptor
                                                                              { iLabel =
                                                                                  Just
                                                                                    "How will you make sure the same reference data will be available to reproduce your results?"
                                                                              , iNumbering = NoNumbering
                                                                              , iIdent = Nothing
                                                                              , iTags = []
                                                                              , iShortDescription = Nothing
                                                                              , iLongDescription =
                                                                                  Just
                                                                                    "<p class=\"question-description\">Will the reference data in the version you use be available to others?</p>"
                                                                              , chapterId = Just 1
                                                                              , questionId = Just 80
                                                                              , iLink = Nothing
                                                                              , iMandatory = True
                                                                              , iRules = []
                                                                              , iAutoComplete = []
                                                                              }
                                                                          , chfiAvailableOptions =
                                                                              [ SimpleOption
                                                                                  "I will keep a copy and make it available with my results"
                                                                              , SimpleOption
                                                                                  "The provider keeps old versions around"
                                                                              ]
                                                                          }
                                                                        ]
                                                                    }
                                                                  ]
                                                              }
                                                            ]
                                                        }
                                                      , SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 1
                                                            , questionId = Just 9
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ MultipleGroup
                                                              { mgDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "What existing non-reference data sets will you use?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription =
                                                                      Just "List all the items bellow."
                                                                  , iLongDescription =
                                                                      Just
                                                                        "<p class=\"question-description\">Even if you will be producing your own data, you often will also be relying on existing data sets (e.g. from earlier . You may need to integrate your new data with an existing data set or retrieve additional information from related data bases. Will you be doing such things?</p>"
                                                                  , chapterId = Just 1
                                                                  , questionId = Just 9
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , mgLevel = 0
                                                              , mgItems =
                                                                  [ StringFI
                                                                    { sfiDescriptor =
                                                                        FIDescriptor
                                                                        { iLabel = Just "Item"
                                                                        , iNumbering = NoNumbering
                                                                        , iIdent = Nothing
                                                                        , iTags = []
                                                                        , iShortDescription = Nothing
                                                                        , iLongDescription =
                                                                            Just
                                                                              "<p class=\"question-description\">Even if you will be producing your own data, you often will also be relying on existing data sets (e.g. from earlier . You may need to integrate your new data with an existing data set or retrieve additional information from related data bases. Will you be doing such things?</p>"
                                                                        , chapterId = Just 1
                                                                        , questionId = Just 9
                                                                        , iLink = Nothing
                                                                        , iMandatory = False
                                                                        , iRules = []
                                                                        , iAutoComplete = []
                                                                        }
                                                                    }
                                                                  , SimpleGroup
                                                                    { sgDescriptor =
                                                                        FIDescriptor
                                                                        { iLabel = Nothing
                                                                        , iNumbering = NoNumbering
                                                                        , iIdent = Nothing
                                                                        , iTags = []
                                                                        , iShortDescription = Nothing
                                                                        , iLongDescription = Nothing
                                                                        , chapterId = Just 1
                                                                        , questionId = Just 11
                                                                        , iLink = Nothing
                                                                        , iMandatory = False
                                                                        , iRules = []
                                                                        , iAutoComplete = []
                                                                        }
                                                                    , sgLevel = 0
                                                                    , sgItems =
                                                                        [ ChoiceFI
                                                                          { chfiDescriptor =
                                                                              FIDescriptor
                                                                              { iLabel =
                                                                                  Just
                                                                                    "Will the owners of this data set work with you on this study"
                                                                              , iNumbering = NoNumbering
                                                                              , iIdent = Nothing
                                                                              , iTags = []
                                                                              , iShortDescription = Nothing
                                                                              , iLongDescription = Nothing
                                                                              , chapterId = Just 1
                                                                              , questionId = Just 11
                                                                              , iLink = Nothing
                                                                              , iMandatory = True
                                                                              , iRules = []
                                                                              , iAutoComplete = []
                                                                              }
                                                                          , chfiAvailableOptions =
                                                                              [ DetailedOption
                                                                                  NoNumbering
                                                                                  "No"
                                                                                  [ SimpleGroup
                                                                                    { sgDescriptor =
                                                                                        FIDescriptor
                                                                                        { iLabel = Nothing
                                                                                        , iNumbering = NoNumbering
                                                                                        , iIdent = Nothing
                                                                                        , iTags = []
                                                                                        , iShortDescription = Nothing
                                                                                        , iLongDescription = Nothing
                                                                                        , chapterId = Just 1
                                                                                        , questionId = Just 11
                                                                                        , iLink = Nothing
                                                                                        , iMandatory = True
                                                                                        , iRules = []
                                                                                        , iAutoComplete = []
                                                                                        }
                                                                                    , sgLevel = 0
                                                                                    , sgItems =
                                                                                        [ SimpleGroup
                                                                                          { sgDescriptor =
                                                                                              FIDescriptor
                                                                                              { iLabel = Nothing
                                                                                              , iNumbering = NoNumbering
                                                                                              , iIdent = Nothing
                                                                                              , iTags = []
                                                                                              , iShortDescription =
                                                                                                  Nothing
                                                                                              , iLongDescription =
                                                                                                  Nothing
                                                                                              , chapterId = Just 1
                                                                                              , questionId = Just 10
                                                                                              , iLink = Nothing
                                                                                              , iMandatory = False
                                                                                              , iRules = []
                                                                                              , iAutoComplete = []
                                                                                              }
                                                                                          , sgLevel = 0
                                                                                          , sgItems =
                                                                                              [ ChoiceFI
                                                                                                { chfiDescriptor =
                                                                                                    FIDescriptor
                                                                                                    { iLabel =
                                                                                                        Just
                                                                                                          "Do you need to request access to the data"
                                                                                                    , iNumbering =
                                                                                                        NoNumbering
                                                                                                    , iIdent = Nothing
                                                                                                    , iTags = []
                                                                                                    , iShortDescription =
                                                                                                        Nothing
                                                                                                    , iLongDescription =
                                                                                                        Nothing
                                                                                                    , chapterId = Just 1
                                                                                                    , questionId =
                                                                                                        Just 10
                                                                                                    , iLink = Nothing
                                                                                                    , iMandatory = True
                                                                                                    , iRules = []
                                                                                                    , iAutoComplete = []
                                                                                                    }
                                                                                                , chfiAvailableOptions =
                                                                                                    [ SimpleOption "No"
                                                                                                    , SimpleOption "Yes"
                                                                                                    ]
                                                                                                }
                                                                                              ]
                                                                                          }
                                                                                        ]
                                                                                    }
                                                                                  ]
                                                                              , SimpleOption "Yes"
                                                                              , SimpleOption "We are the owners"
                                                                              ]
                                                                          }
                                                                        ]
                                                                    }
                                                                  , SimpleGroup
                                                                    { sgDescriptor =
                                                                        FIDescriptor
                                                                        { iLabel = Nothing
                                                                        , iNumbering = NoNumbering
                                                                        , iIdent = Nothing
                                                                        , iTags = []
                                                                        , iShortDescription = Nothing
                                                                        , iLongDescription = Nothing
                                                                        , chapterId = Just 1
                                                                        , questionId = Just 12
                                                                        , iLink = Nothing
                                                                        , iMandatory = False
                                                                        , iRules = []
                                                                        , iAutoComplete = []
                                                                        }
                                                                    , sgLevel = 0
                                                                    , sgItems =
                                                                        [ ChoiceFI
                                                                          { chfiDescriptor =
                                                                              FIDescriptor
                                                                              { iLabel =
                                                                                  Just
                                                                                    "Is extension of any consent for privacy sensitive data needed?"
                                                                              , iNumbering = NoNumbering
                                                                              , iIdent = Nothing
                                                                              , iTags = []
                                                                              , iShortDescription = Nothing
                                                                              , iLongDescription =
                                                                                  Just
                                                                                    "<p class=\"question-description\">If the data that you will re-use is coupled to people, is the informed consent that was originally obtained from those people covering your current research?</p>"
                                                                              , chapterId = Just 1
                                                                              , questionId = Just 12
                                                                              , iLink = Nothing
                                                                              , iMandatory = True
                                                                              , iRules = []
                                                                              , iAutoComplete = []
                                                                              }
                                                                          , chfiAvailableOptions =
                                                                              [ SimpleOption "Not applicable"
                                                                              , SimpleOption "Existing consent applies"
                                                                              , SimpleOption "New consent needed"
                                                                              ]
                                                                          }
                                                                        ]
                                                                    }
                                                                  , SimpleGroup
                                                                    { sgDescriptor =
                                                                        FIDescriptor
                                                                        { iLabel = Nothing
                                                                        , iNumbering = NoNumbering
                                                                        , iIdent = Nothing
                                                                        , iTags = []
                                                                        , iShortDescription = Nothing
                                                                        , iLongDescription = Nothing
                                                                        , chapterId = Just 1
                                                                        , questionId = Just 13
                                                                        , iLink = Nothing
                                                                        , iMandatory = False
                                                                        , iRules = []
                                                                        , iAutoComplete = []
                                                                        }
                                                                    , sgLevel = 0
                                                                    , sgItems =
                                                                        [ ChoiceFI
                                                                          { chfiDescriptor =
                                                                              FIDescriptor
                                                                              { iLabel =
                                                                                  Just
                                                                                    "Will any usage restrictions affect your reuse?"
                                                                              , iNumbering = NoNumbering
                                                                              , iIdent = Nothing
                                                                              , iTags = []
                                                                              , iShortDescription = Nothing
                                                                              , iLongDescription = Nothing
                                                                              , chapterId = Just 1
                                                                              , questionId = Just 13
                                                                              , iLink = Nothing
                                                                              , iMandatory = True
                                                                              , iRules = []
                                                                              , iAutoComplete = []
                                                                              }
                                                                          , chfiAvailableOptions =
                                                                              [SimpleOption "No", SimpleOption "Yes"]
                                                                          }
                                                                        ]
                                                                    }
                                                                  , SimpleGroup
                                                                    { sgDescriptor =
                                                                        FIDescriptor
                                                                        { iLabel = Nothing
                                                                        , iNumbering = NoNumbering
                                                                        , iIdent = Nothing
                                                                        , iTags = []
                                                                        , iShortDescription = Nothing
                                                                        , iLongDescription = Nothing
                                                                        , chapterId = Just 1
                                                                        , questionId = Just 14
                                                                        , iLink = Nothing
                                                                        , iMandatory = False
                                                                        , iRules = []
                                                                        , iAutoComplete = []
                                                                        }
                                                                    , sgLevel = 0
                                                                    , sgItems =
                                                                        [ ChoiceFI
                                                                          { chfiDescriptor =
                                                                              FIDescriptor
                                                                              { iLabel =
                                                                                  Just
                                                                                    "How will you be accessing the data?"
                                                                              , iNumbering = NoNumbering
                                                                              , iIdent = Nothing
                                                                              , iTags = []
                                                                              , iShortDescription = Nothing
                                                                              , iLongDescription = Nothing
                                                                              , chapterId = Just 1
                                                                              , questionId = Just 14
                                                                              , iLink = Nothing
                                                                              , iMandatory = True
                                                                              , iRules = []
                                                                              , iAutoComplete = []
                                                                              }
                                                                          , chfiAvailableOptions =
                                                                              [ SimpleOption
                                                                                  "Already have physical copy"
                                                                              , SimpleOption "Will make physical copy"
                                                                              , SimpleOption "Will use it online"
                                                                              ]
                                                                          }
                                                                        ]
                                                                    }
                                                                  , SimpleGroup
                                                                    { sgDescriptor =
                                                                        FIDescriptor
                                                                        { iLabel = Nothing
                                                                        , iNumbering = NoNumbering
                                                                        , iIdent = Nothing
                                                                        , iTags = []
                                                                        , iShortDescription = Nothing
                                                                        , iLongDescription = Nothing
                                                                        , chapterId = Just 1
                                                                        , questionId = Just 15
                                                                        , iLink = Nothing
                                                                        , iMandatory = False
                                                                        , iRules = []
                                                                        , iAutoComplete = []
                                                                        }
                                                                    , sgLevel = 0
                                                                    , sgItems =
                                                                        [ ChoiceFI
                                                                          { chfiDescriptor =
                                                                              FIDescriptor
                                                                              { iLabel =
                                                                                  Just
                                                                                    "Do you knpw in what format the data is available?"
                                                                              , iNumbering = NoNumbering
                                                                              , iIdent = Nothing
                                                                              , iTags = []
                                                                              , iShortDescription = Nothing
                                                                              , iLongDescription =
                                                                                  Just
                                                                                    "<p class=\"question-description\">Do you know the data format of the data? Is this suitable for your work? Does it need to be converted?</p>"
                                                                              , chapterId = Just 1
                                                                              , questionId = Just 15
                                                                              , iLink = Nothing
                                                                              , iMandatory = True
                                                                              , iRules = []
                                                                              , iAutoComplete = []
                                                                              }
                                                                          , chfiAvailableOptions =
                                                                              [ SimpleOption "I can directly use it"
                                                                              , SimpleOption
                                                                                  "I need to convert it before using"
                                                                              ]
                                                                          }
                                                                        ]
                                                                    }
                                                                  , SimpleGroup
                                                                    { sgDescriptor =
                                                                        FIDescriptor
                                                                        { iLabel = Nothing
                                                                        , iNumbering = NoNumbering
                                                                        , iIdent = Nothing
                                                                        , iTags = []
                                                                        , iShortDescription = Nothing
                                                                        , iLongDescription = Nothing
                                                                        , chapterId = Just 1
                                                                        , questionId = Just 17
                                                                        , iLink = Nothing
                                                                        , iMandatory = False
                                                                        , iRules = []
                                                                        , iAutoComplete = []
                                                                        }
                                                                    , sgLevel = 0
                                                                    , sgItems =
                                                                        [ ChoiceFI
                                                                          { chfiDescriptor =
                                                                              FIDescriptor
                                                                              { iLabel =
                                                                                  Just
                                                                                    "Is the data set fixed, or will it be updated in the future?"
                                                                              , iNumbering = NoNumbering
                                                                              , iIdent = Nothing
                                                                              , iTags = []
                                                                              , iShortDescription = Nothing
                                                                              , iLongDescription =
                                                                                  Just
                                                                                    "<p class=\"question-description\">Is the data set you will reuse a fixed data set (with a persistent identifier), or is it a data set that is being worked on (by others) and may be updated during your project or after?</p>"
                                                                              , chapterId = Just 1
                                                                              , questionId = Just 17
                                                                              , iLink = Nothing
                                                                              , iMandatory = True
                                                                              , iRules = []
                                                                              , iAutoComplete = []
                                                                              }
                                                                          , chfiAvailableOptions =
                                                                              [ SimpleOption
                                                                                  "It is a fixed data set, this will not influence reproducibility of my results"
                                                                              , SimpleOption
                                                                                  "It may change, I will make sure a copy of the version I used will be available with my results"
                                                                              ]
                                                                          }
                                                                        ]
                                                                    }
                                                                  , SimpleGroup
                                                                    { sgDescriptor =
                                                                        FIDescriptor
                                                                        { iLabel = Nothing
                                                                        , iNumbering = NoNumbering
                                                                        , iIdent = Nothing
                                                                        , iTags = []
                                                                        , iShortDescription = Nothing
                                                                        , iLongDescription = Nothing
                                                                        , chapterId = Just 1
                                                                        , questionId = Just 18
                                                                        , iLink = Nothing
                                                                        , iMandatory = False
                                                                        , iRules = []
                                                                        , iAutoComplete = []
                                                                        }
                                                                    , sgLevel = 0
                                                                    , sgItems =
                                                                        [ ChoiceFI
                                                                          { chfiDescriptor =
                                                                              FIDescriptor
                                                                              { iLabel =
                                                                                  Just
                                                                                    "Can you and will you use the complete existing data set?"
                                                                              , iNumbering = NoNumbering
                                                                              , iIdent = Nothing
                                                                              , iTags = []
                                                                              , iShortDescription = Nothing
                                                                              , iLongDescription =
                                                                                  Just
                                                                                    "<p class=\"question-description\">If you use any filtering, how will you make sure that your results will be reproducible by yourself and others at a later time?</p>"
                                                                              , chapterId = Just 1
                                                                              , questionId = Just 18
                                                                              , iLink = Nothing
                                                                              , iMandatory = True
                                                                              , iRules = []
                                                                              , iAutoComplete = []
                                                                              }
                                                                          , chfiAvailableOptions =
                                                                              [ SimpleOption
                                                                                  "I will use the complete data set"
                                                                              , SimpleOption
                                                                                  "Any filtering or selection will be well documented"
                                                                              , SimpleOption
                                                                                  "I will make sure the selected subset will be available together with my results"
                                                                              ]
                                                                          }
                                                                        ]
                                                                    }
                                                                  ]
                                                              }
                                                            ]
                                                        }
                                                      , SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 1
                                                            , questionId = Just 42
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "Will you couple existing (biobank) data sets?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription = Nothing
                                                                  , chapterId = Just 1
                                                                  , questionId = Just 42
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [ SimpleOption "No"
                                                                  , DetailedOption
                                                                      NoNumbering
                                                                      "Yes"
                                                                      [ SimpleGroup
                                                                        { sgDescriptor =
                                                                            FIDescriptor
                                                                            { iLabel = Nothing
                                                                            , iNumbering = NoNumbering
                                                                            , iIdent = Nothing
                                                                            , iTags = []
                                                                            , iShortDescription = Nothing
                                                                            , iLongDescription = Nothing
                                                                            , chapterId = Just 1
                                                                            , questionId = Just 42
                                                                            , iLink = Nothing
                                                                            , iMandatory = True
                                                                            , iRules = []
                                                                            , iAutoComplete = []
                                                                            }
                                                                        , sgLevel = 0
                                                                        , sgItems =
                                                                            [ SimpleGroup
                                                                              { sgDescriptor =
                                                                                  FIDescriptor
                                                                                  { iLabel = Nothing
                                                                                  , iNumbering = NoNumbering
                                                                                  , iIdent = Nothing
                                                                                  , iTags = []
                                                                                  , iShortDescription = Nothing
                                                                                  , iLongDescription = Nothing
                                                                                  , chapterId = Just 1
                                                                                  , questionId = Just 43
                                                                                  , iLink = Nothing
                                                                                  , iMandatory = False
                                                                                  , iRules = []
                                                                                  , iAutoComplete = []
                                                                                  }
                                                                              , sgLevel = 0
                                                                              , sgItems =
                                                                                  [ ChoiceFI
                                                                                    { chfiDescriptor =
                                                                                        FIDescriptor
                                                                                        { iLabel =
                                                                                            Just
                                                                                              "Will you use deterministic couplings?"
                                                                                        , iNumbering = NoNumbering
                                                                                        , iIdent = Nothing
                                                                                        , iTags = []
                                                                                        , iShortDescription = Nothing
                                                                                        , iLongDescription =
                                                                                            Just
                                                                                              "<p class=\"question-description\">Data sets that have exactly identical fields that are well filled can be coupled using deterministic methods. Will you be using such methods?</p>"
                                                                                        , chapterId = Just 1
                                                                                        , questionId = Just 43
                                                                                        , iLink = Nothing
                                                                                        , iMandatory = True
                                                                                        , iRules = []
                                                                                        , iAutoComplete = []
                                                                                        }
                                                                                    , chfiAvailableOptions =
                                                                                        [ SimpleOption "No"
                                                                                        , SimpleOption "Yes"
                                                                                        ]
                                                                                    }
                                                                                  ]
                                                                              }
                                                                            , SimpleGroup
                                                                              { sgDescriptor =
                                                                                  FIDescriptor
                                                                                  { iLabel = Nothing
                                                                                  , iNumbering = NoNumbering
                                                                                  , iIdent = Nothing
                                                                                  , iTags = []
                                                                                  , iShortDescription = Nothing
                                                                                  , iLongDescription = Nothing
                                                                                  , chapterId = Just 1
                                                                                  , questionId = Just 44
                                                                                  , iLink = Nothing
                                                                                  , iMandatory = False
                                                                                  , iRules = []
                                                                                  , iAutoComplete = []
                                                                                  }
                                                                              , sgLevel = 0
                                                                              , sgItems =
                                                                                  [ TextFI
                                                                                    { tfiDescriptor =
                                                                                        FIDescriptor
                                                                                        { iLabel =
                                                                                            Just
                                                                                              "Will you be using a trusted third party for coupling?"
                                                                                        , iNumbering = NoNumbering
                                                                                        , iIdent = Nothing
                                                                                        , iTags = []
                                                                                        , iShortDescription = Nothing
                                                                                        , iLongDescription =
                                                                                            Just
                                                                                              "What will be the procedure that is followed? Where will what data be sent? Did a legal advisor look at the procedures?"
                                                                                        , chapterId = Just 1
                                                                                        , questionId = Just 44
                                                                                        , iLink = Nothing
                                                                                        , iMandatory = True
                                                                                        , iRules = []
                                                                                        , iAutoComplete = []
                                                                                        }
                                                                                    }
                                                                                  ]
                                                                              }
                                                                            , SimpleGroup
                                                                              { sgDescriptor =
                                                                                  FIDescriptor
                                                                                  { iLabel = Nothing
                                                                                  , iNumbering = NoNumbering
                                                                                  , iIdent = Nothing
                                                                                  , iTags = []
                                                                                  , iShortDescription = Nothing
                                                                                  , iLongDescription = Nothing
                                                                                  , chapterId = Just 1
                                                                                  , questionId = Just 45
                                                                                  , iLink = Nothing
                                                                                  , iMandatory = False
                                                                                  , iRules = []
                                                                                  , iAutoComplete = []
                                                                                  }
                                                                              , sgLevel = 0
                                                                              , sgItems =
                                                                                  [ ChoiceFI
                                                                                    { chfiDescriptor =
                                                                                        FIDescriptor
                                                                                        { iLabel =
                                                                                            Just
                                                                                              "Is consent available for the couplings?"
                                                                                        , iNumbering = NoNumbering
                                                                                        , iIdent = Nothing
                                                                                        , iTags = []
                                                                                        , iShortDescription = Nothing
                                                                                        , iLongDescription = Nothing
                                                                                        , chapterId = Just 1
                                                                                        , questionId = Just 45
                                                                                        , iLink = Nothing
                                                                                        , iMandatory = True
                                                                                        , iRules = []
                                                                                        , iAutoComplete = []
                                                                                        }
                                                                                    , chfiAvailableOptions =
                                                                                        [ SimpleOption "No"
                                                                                        , SimpleOption "Yes"
                                                                                        ]
                                                                                    }
                                                                                  ]
                                                                              }
                                                                            , SimpleGroup
                                                                              { sgDescriptor =
                                                                                  FIDescriptor
                                                                                  { iLabel = Nothing
                                                                                  , iNumbering = NoNumbering
                                                                                  , iIdent = Nothing
                                                                                  , iTags = []
                                                                                  , iShortDescription = Nothing
                                                                                  , iLongDescription = Nothing
                                                                                  , chapterId = Just 1
                                                                                  , questionId = Just 46
                                                                                  , iLink = Nothing
                                                                                  , iMandatory = False
                                                                                  , iRules = []
                                                                                  , iAutoComplete = []
                                                                                  }
                                                                              , sgLevel = 0
                                                                              , sgItems =
                                                                                  [ TextFI
                                                                                    { tfiDescriptor =
                                                                                        FIDescriptor
                                                                                        { iLabel =
                                                                                            Just
                                                                                              "How will you check whether your coupled data are representative of your goal population?"
                                                                                        , iNumbering = NoNumbering
                                                                                        , iIdent = Nothing
                                                                                        , iTags = []
                                                                                        , iShortDescription = Nothing
                                                                                        , iLongDescription =
                                                                                            Just
                                                                                              "Sometimes, through the nature of the data sets that are coupled, the coupled set is no longer representative for the whole population (e.g. some fields may only have been filled for people with high blood pressure). This can disturb your research if undetected. How will you make sure this is not happening?"
                                                                                        , chapterId = Just 1
                                                                                        , questionId = Just 46
                                                                                        , iLink = Nothing
                                                                                        , iMandatory = True
                                                                                        , iRules = []
                                                                                        , iAutoComplete = []
                                                                                        }
                                                                                    }
                                                                                  ]
                                                                              }
                                                                            , SimpleGroup
                                                                              { sgDescriptor =
                                                                                  FIDescriptor
                                                                                  { iLabel = Nothing
                                                                                  , iNumbering = NoNumbering
                                                                                  , iIdent = Nothing
                                                                                  , iTags = []
                                                                                  , iShortDescription = Nothing
                                                                                  , iLongDescription = Nothing
                                                                                  , chapterId = Just 1
                                                                                  , questionId = Just 47
                                                                                  , iLink = Nothing
                                                                                  , iMandatory = False
                                                                                  , iRules = []
                                                                                  , iAutoComplete = []
                                                                                  }
                                                                              , sgLevel = 0
                                                                              , sgItems =
                                                                                  [ ChoiceFI
                                                                                    { chfiDescriptor =
                                                                                        FIDescriptor
                                                                                        { iLabel =
                                                                                            Just
                                                                                              "What is the goal of the coupling?"
                                                                                        , iNumbering = NoNumbering
                                                                                        , iIdent = Nothing
                                                                                        , iTags = []
                                                                                        , iShortDescription = Nothing
                                                                                        , iLongDescription = Nothing
                                                                                        , chapterId = Just 1
                                                                                        , questionId = Just 47
                                                                                        , iLink = Nothing
                                                                                        , iMandatory = True
                                                                                        , iRules = []
                                                                                        , iAutoComplete = []
                                                                                        }
                                                                                    , chfiAvailableOptions =
                                                                                        [ SimpleOption
                                                                                            "More data about the same subjects (intersection)"
                                                                                        , SimpleOption
                                                                                            "Enlarging the group of subjects (union)"
                                                                                        ]
                                                                                    }
                                                                                  ]
                                                                              }
                                                                            , SimpleGroup
                                                                              { sgDescriptor =
                                                                                  FIDescriptor
                                                                                  { iLabel = Nothing
                                                                                  , iNumbering = NoNumbering
                                                                                  , iIdent = Nothing
                                                                                  , iTags = []
                                                                                  , iShortDescription = Nothing
                                                                                  , iLongDescription = Nothing
                                                                                  , chapterId = Just 1
                                                                                  , questionId = Just 48
                                                                                  , iLink = Nothing
                                                                                  , iMandatory = False
                                                                                  , iRules = []
                                                                                  , iAutoComplete = []
                                                                                  }
                                                                              , sgLevel = 0
                                                                              , sgItems =
                                                                                  [ TextFI
                                                                                    { tfiDescriptor =
                                                                                        FIDescriptor
                                                                                        { iLabel =
                                                                                            Just
                                                                                              "What variable(s) will you be using for the coupling?"
                                                                                        , iNumbering = NoNumbering
                                                                                        , iIdent = Nothing
                                                                                        , iTags = []
                                                                                        , iShortDescription = Nothing
                                                                                        , iLongDescription = Nothing
                                                                                        , chapterId = Just 1
                                                                                        , questionId = Just 48
                                                                                        , iLink = Nothing
                                                                                        , iMandatory = True
                                                                                        , iRules = []
                                                                                        , iAutoComplete = []
                                                                                        }
                                                                                    }
                                                                                  ]
                                                                              }
                                                                            , SimpleGroup
                                                                              { sgDescriptor =
                                                                                  FIDescriptor
                                                                                  { iLabel = Nothing
                                                                                  , iNumbering = NoNumbering
                                                                                  , iIdent = Nothing
                                                                                  , iTags = []
                                                                                  , iShortDescription = Nothing
                                                                                  , iLongDescription = Nothing
                                                                                  , chapterId = Just 1
                                                                                  , questionId = Just 49
                                                                                  , iLink = Nothing
                                                                                  , iMandatory = False
                                                                                  , iRules = []
                                                                                  , iAutoComplete = []
                                                                                  }
                                                                              , sgLevel = 0
                                                                              , sgItems =
                                                                                  [ ChoiceFI
                                                                                    { chfiDescriptor =
                                                                                        FIDescriptor
                                                                                        { iLabel =
                                                                                            Just
                                                                                              "Will you use probabilistic couplings?"
                                                                                        , iNumbering = NoNumbering
                                                                                        , iIdent = Nothing
                                                                                        , iTags = []
                                                                                        , iShortDescription = Nothing
                                                                                        , iLongDescription =
                                                                                            Just
                                                                                              "<p class=\"question-description\">Data sets that have similar but not identical fields or with identical fields that are not consistently filled can be coupled using probabilistic methods. Will you be using such methods?</p>"
                                                                                        , chapterId = Just 1
                                                                                        , questionId = Just 49
                                                                                        , iLink = Nothing
                                                                                        , iMandatory = True
                                                                                        , iRules = []
                                                                                        , iAutoComplete = []
                                                                                        }
                                                                                    , chfiAvailableOptions =
                                                                                        [ SimpleOption "No"
                                                                                        , SimpleOption "Yes"
                                                                                        ]
                                                                                    }
                                                                                  ]
                                                                              }
                                                                            ]
                                                                        }
                                                                      ]
                                                                  ]
                                                              }
                                                            ]
                                                        }
                                                      ]
                                                  }
                                                ]
                                            ]
                                        }
                                      , SimpleGroup
                                        { sgDescriptor =
                                            FIDescriptor
                                            { iLabel = Nothing
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription = Nothing
                                            , chapterId = Just 1
                                            , questionId = Just 16
                                            , iLink = Nothing
                                            , iMandatory = False
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , sgLevel = 0
                                        , sgItems =
                                            [ ChoiceFI
                                              { chfiDescriptor =
                                                  FIDescriptor
                                                  { iLabel =
                                                      Just
                                                        "Do you need to harmonize different sources of existing data?"
                                                  , iNumbering = NoNumbering
                                                  , iIdent = Nothing
                                                  , iTags = []
                                                  , iShortDescription = Nothing
                                                  , iLongDescription =
                                                      Just
                                                        "<p class=\"question-description\">If you are combining data from different sources, harmonization may be required. You may need to re-analyse some original data.</p>"
                                                  , chapterId = Just 1
                                                  , questionId = Just 16
                                                  , iLink = Nothing
                                                  , iMandatory = True
                                                  , iRules = []
                                                  , iAutoComplete = []
                                                  }
                                              , chfiAvailableOptions = [SimpleOption "No", SimpleOption "Yes"]
                                              }
                                            ]
                                        }
                                      , SimpleGroup
                                        { sgDescriptor =
                                            FIDescriptor
                                            { iLabel = Nothing
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription = Nothing
                                            , chapterId = Just 1
                                            , questionId = Just 81
                                            , iLink = Nothing
                                            , iMandatory = False
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , sgLevel = 0
                                        , sgItems =
                                            [ ChoiceFI
                                              { chfiDescriptor =
                                                  FIDescriptor
                                                  { iLabel =
                                                      Just
                                                        "Will you be using data that needs to be (re-)made computer readable first?"
                                                  , iNumbering = NoNumbering
                                                  , iIdent = Nothing
                                                  , iTags = []
                                                  , iShortDescription = Nothing
                                                  , iLongDescription =
                                                      Just
                                                        "<p class=\"question-description\">Some old data may need to be recovered, e.g. from tables in scientific papers or may be punch cards.</p>"
                                                  , chapterId = Just 1
                                                  , questionId = Just 81
                                                  , iLink = Nothing
                                                  , iMandatory = True
                                                  , iRules = []
                                                  , iAutoComplete = []
                                                  }
                                              , chfiAvailableOptions =
                                                  [ SimpleOption "No"
                                                  , SimpleOption
                                                      "Yes, I will make sure to make this data available with my results."
                                                  ]
                                              }
                                            ]
                                        }
                                      ]
                                  }
                                ]
                            }
                          ]
                      ]
                  }
                ]
            }
          , SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 1
                , questionId = Just 29
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "Will reference data be created?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription =
                          Just
                            "<p class=\"question-description\">Will any of the data that you will be creating form a reference data set for future research (by others)?</p>"
                      , chapterId = Just 1
                      , questionId = Just 29
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions =
                      [ SimpleOption "No"
                      , DetailedOption
                          NoNumbering
                          "Yes"
                          [ SimpleGroup
                            { sgDescriptor =
                                FIDescriptor
                                { iLabel = Nothing
                                , iNumbering = NoNumbering
                                , iIdent = Nothing
                                , iTags = []
                                , iShortDescription = Nothing
                                , iLongDescription = Nothing
                                , chapterId = Just 1
                                , questionId = Just 29
                                , iLink = Nothing
                                , iMandatory = True
                                , iRules = []
                                , iAutoComplete = []
                                }
                            , sgLevel = 0
                            , sgItems =
                                [ SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 1
                                      , questionId = Just 30
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ TextFI
                                        { tfiDescriptor =
                                            FIDescriptor
                                            { iLabel = Just "What will the Intellectual Property be like?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription =
                                                Just
                                                  "Who will own the rights to the reference data set? Who will be able to use it?"
                                            , chapterId = Just 1
                                            , questionId = Just 30
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 1
                                      , questionId = Just 31
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ TextFI
                                        { tfiDescriptor =
                                            FIDescriptor
                                            { iLabel = Just "How will you maintain it?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription =
                                                Just
                                                  "How will maintenance be paid for in the long run? Will you host it yourself or deposit it with a repository? How will you deal with requests for help? And with requests for adding data?"
                                            , chapterId = Just 1
                                            , questionId = Just 31
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 1
                                      , questionId = Just 32
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ TextFI
                                        { tfiDescriptor =
                                            FIDescriptor
                                            { iLabel = Just "How will the release schedule be?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription =
                                                Just "Will you be updating the reference data at regular intervals?"
                                            , chapterId = Just 1
                                            , questionId = Just 32
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        }
                                      ]
                                  }
                                ]
                            }
                          ]
                      ]
                  }
                ]
            }
          , SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 1
                , questionId = Just 33
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "Will you be storing samples?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , chapterId = Just 1
                      , questionId = Just 33
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions = [SimpleOption "No", SimpleOption "Yes"]
                  }
                ]
            }
          , SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 1
                , questionId = Just 38
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "Will you be collecting experimental data?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , chapterId = Just 1
                      , questionId = Just 38
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions = [SimpleOption "No", SimpleOption "Yes"]
                  }
                ]
            }
          ]
      }
    , Chapter
      { chDescriptor =
          FIDescriptor
          { iLabel = Just "Data design and planning"
          , iNumbering = NoNumbering
          , iIdent = Nothing
          , iTags = []
          , iShortDescription = Nothing
          , iLongDescription = Nothing
          , chapterId = Just 2
          , questionId = Nothing
          , iLink = Nothing
          , iMandatory = False
          , iRules = []
          , iAutoComplete = []
          }
      , chItems =
          [ InfoFI
            { ifiDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 2
                , questionId = Nothing
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , ifiText =
                "In the data design and planning phase, we will make sure that we know what data comes when, that we have enough storage space and compute power to deal with it, and that all the responsibilities have been taken care of."
            }
          , SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 2
                , questionId = Just 1
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "Have you identified types of data that you will use that are used by others too?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription =
                          Just
                            "<p class=\"question-description\">Some types of data (e.g. genetic variants in the life sciences) are used by many different projects. For such data, often common standards exist that help to make these data reusable. Are you using such common data formats?</p>"
                      , chapterId = Just 2
                      , questionId = Just 1
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions =
                      [ SimpleOption "No, I am not using any common data types"
                      , SimpleOption "Yes, I will make sure to use common formats for common data types"
                      ]
                  }
                ]
            }
          , SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 2
                , questionId = Just 2
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "Will you be using new types of data?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription =
                          Just
                            "<p class=\"question-description\">Sometimes the type of data you collect can not be stored in a commonly used data format. In such cases you may need to make your own, keeping interoperability as high as possible.</p>"
                      , chapterId = Just 2
                      , questionId = Just 2
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions =
                      [ SimpleOption "No, all of my data will fit in common formats"
                      , DetailedOption
                          NoNumbering
                          "Yes, I will need to use custom formats for some of my data"
                          [ SimpleGroup
                            { sgDescriptor =
                                FIDescriptor
                                { iLabel = Nothing
                                , iNumbering = NoNumbering
                                , iIdent = Nothing
                                , iTags = []
                                , iShortDescription = Nothing
                                , iLongDescription = Nothing
                                , chapterId = Just 2
                                , questionId = Just 2
                                , iLink = Nothing
                                , iMandatory = True
                                , iRules = []
                                , iAutoComplete = []
                                }
                            , sgLevel = 0
                            , sgItems =
                                [ SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 7
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel =
                                                Just
                                                  "Will you need to add fields in your data format to a data type registry?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription =
                                                Just
                                                  "<p class=\"question-description\">Even if the data format you are using is unique to your project, the discrete data items should be reused or reusable as much as possible. Data type registries can help with that.</p>"
                                            , chapterId = Just 2
                                            , questionId = Just 7
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions =
                                            [ SimpleOption
                                                "No, all of my data types are described in a data type registry already"
                                            , SimpleOption "Yes, I will add new types to an existing data type registry"
                                            , SimpleOption "Yes, I will create my own data type registry"
                                            ]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 8
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel =
                                                Just
                                                  "Do you need to create vocabularies or ontologies for any of your data items?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription =
                                                Just
                                                  "<p class=\"question-description\">For good interoperability the use of controlled vocabularies for each discrete data item is advisable. If such vocabularies exist, it is best to reuse those.</p>"
                                            , chapterId = Just 2
                                            , questionId = Just 8
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions =
                                            [ SimpleOption
                                                "No, suitable public controlled vocabularies or ontologies exist for all of my data types"
                                            , SimpleOption
                                                "Yes, I will make and publish a vocabulary or ontology for some of my data"
                                            ]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 9
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ TextFI
                                        { tfiDescriptor =
                                            FIDescriptor
                                            { iLabel = Just "Which data type registries will you use?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription = Nothing
                                            , chapterId = Just 2
                                            , questionId = Just 9
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 10
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel = Just "How will you design your new data format?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription = Nothing
                                            , chapterId = Just 2
                                            , questionId = Just 10
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions =
                                            [ SimpleOption
                                                "There is a closely related more generic and open format that I can specialize"
                                            , SimpleOption "I will use a Linked Data format"
                                            , SimpleOption "I will use a completely custom data format"
                                            ]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 11
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel = Just "Will you describe your new data format for others?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription = Nothing
                                            , chapterId = Just 2
                                            , questionId = Just 11
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions =
                                            [ SimpleOption "No, this is not needed"
                                            , SimpleOption
                                                "Yes, I will register my standards at a data standards registry"
                                            ]
                                        }
                                      ]
                                  }
                                ]
                            }
                          ]
                      ]
                  }
                ]
            }
          , SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 2
                , questionId = Just 3
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "How will you be storing metadata?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription =
                          Just
                            "<p class=\"question-description\">For the re-usability of your data by yourself or others at a later stage, a lot of information about the data, how it was collected and how it can be used should be stored with the data. Such data about the data is called metadata, and this set of questions are about this metadata</p>"
                      , chapterId = Just 2
                      , questionId = Just 3
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions =
                      [ SimpleOption "Skip"
                      , DetailedOption
                          NoNumbering
                          "Explore"
                          [ SimpleGroup
                            { sgDescriptor =
                                FIDescriptor
                                { iLabel = Nothing
                                , iNumbering = NoNumbering
                                , iIdent = Nothing
                                , iTags = []
                                , iShortDescription = Nothing
                                , iLongDescription = Nothing
                                , chapterId = Just 2
                                , questionId = Just 3
                                , iLink = Nothing
                                , iMandatory = True
                                , iRules = []
                                , iAutoComplete = []
                                }
                            , sgLevel = 0
                            , sgItems =
                                [ SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 12
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel =
                                                Just
                                                  "Do suitable 'Minimal Metadata About ...' (MIA...) standards exist for your experiments?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription = Nothing
                                            , chapterId = Just 2
                                            , questionId = Just 12
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions = [SimpleOption "No", SimpleOption "Yes"]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 13
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel =
                                                Just
                                                  "Will you consider re-usability of your data beyond your original purpose?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription =
                                                Just
                                                  "<p class=\"question-description\">Adding more than the strict minimum metadata about your experiment will possibly allow more wide re-use of your data, with associated higher data citation rates. Please note that it is not easy for yourself to see all other ways in which others could be reusing your data.</p>"
                                            , chapterId = Just 2
                                            , questionId = Just 13
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions =
                                            [ SimpleOption "No, I will just document the bare minimum"
                                            , DetailedOption
                                                NoNumbering
                                                "Yes, I will document more metadata than needed for reproducibility"
                                                [ SimpleGroup
                                                  { sgDescriptor =
                                                      FIDescriptor
                                                      { iLabel = Nothing
                                                      , iNumbering = NoNumbering
                                                      , iIdent = Nothing
                                                      , iTags = []
                                                      , iShortDescription = Nothing
                                                      , iLongDescription = Nothing
                                                      , chapterId = Just 2
                                                      , questionId = Just 13
                                                      , iLink = Nothing
                                                      , iMandatory = True
                                                      , iRules = []
                                                      , iAutoComplete = []
                                                      }
                                                  , sgLevel = 0
                                                  , sgItems =
                                                      [ SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 14
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "How will you balance the extra efforts with the potential for added reusability?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription = Nothing
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 14
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [ SimpleOption "I will see what I can do"
                                                                  , SimpleOption
                                                                      "I will use preselected additional standard modules of metadata"
                                                                  , SimpleOption
                                                                      "I will store all metadata I can gather and document"
                                                                  ]
                                                              }
                                                            ]
                                                        }
                                                      , SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 15
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "Do you need to exchange your data with others?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription = Nothing
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 15
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [SimpleOption "No", SimpleOption "Yes"]
                                                              }
                                                            ]
                                                        }
                                                      ]
                                                  }
                                                ]
                                            ]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 16
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel = Just "Did you consider how to monitor data integrity?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription =
                                                Just
                                                  "<p class=\"question-description\">Working with large amounts of heterogenous data in a larger research group has implications for the data integrity. How do you make sure every step of the workflow is done with the right version of the data? How do you handle the situation when a mistake is uncovered? Will you be able to redo the strict minimum data handling?</p>"
                                            , chapterId = Just 2
                                            , questionId = Just 16
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions =
                                            [ SimpleOption "Skip"
                                            , DetailedOption
                                                NoNumbering
                                                "Explore"
                                                [ SimpleGroup
                                                  { sgDescriptor =
                                                      FIDescriptor
                                                      { iLabel = Nothing
                                                      , iNumbering = NoNumbering
                                                      , iIdent = Nothing
                                                      , iTags = []
                                                      , iShortDescription = Nothing
                                                      , iLongDescription = Nothing
                                                      , chapterId = Just 2
                                                      , questionId = Just 16
                                                      , iLink = Nothing
                                                      , iMandatory = True
                                                      , iRules = []
                                                      , iAutoComplete = []
                                                      }
                                                  , sgLevel = 0
                                                  , sgItems =
                                                      [ SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 17
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "Will you be keeping a master list with checksums of certified/correct/canonical/verified data?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription =
                                                                      Just
                                                                        "<p class=\"question-description\">Data corruption or mistakes can happen with large amounts of files or large files. Keeping a master list with data checksums can be helpful to prevent expensive mistakes. It can also be helpful to keep the sample list under version control forcing that all changes are well documented.</p>"
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 17
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [SimpleOption "No", SimpleOption "Yes"]
                                                              }
                                                            ]
                                                        }
                                                      , SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 18
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "Will you define a way to detect file or sample swaps, e.g. by measuring something independently?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription = Nothing
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 18
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [SimpleOption "No", SimpleOption "Yes"]
                                                              }
                                                            ]
                                                        }
                                                      ]
                                                  }
                                                ]
                                            ]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 20
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel = Just "Do all datasets you work with have a license?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription =
                                                Just
                                                  "<p class=\"question-description\">It is not always clear to everyone in the project (ad outside) what can and can not be done with a data set. It is helpful to associate each data set with a license as early as possible in the project. A data license should ideally be as free as possible: any restriction like 'only for non-commercial use' or 'attribution required' may reduce the reusability and thereby the number of citations. If possible, use a computer-readable and computer actionable license.</p>"
                                            , chapterId = Just 2
                                            , questionId = Just 20
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions =
                                            [ SimpleOption "No"
                                            , DetailedOption
                                                NoNumbering
                                                "Yes"
                                                [ SimpleGroup
                                                  { sgDescriptor =
                                                      FIDescriptor
                                                      { iLabel = Nothing
                                                      , iNumbering = NoNumbering
                                                      , iIdent = Nothing
                                                      , iTags = []
                                                      , iShortDescription = Nothing
                                                      , iLongDescription = Nothing
                                                      , chapterId = Just 2
                                                      , questionId = Just 20
                                                      , iLink = Nothing
                                                      , iMandatory = True
                                                      , iRules = []
                                                      , iAutoComplete = []
                                                      }
                                                  , sgLevel = 0
                                                  , sgItems =
                                                      [ SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 19
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "Will you store the licenses with the data at all time?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription =
                                                                      Just
                                                                        "<p class=\"question-description\">It is very likely that data will be moved and copied. At some point people may lose track of the origins. It can be helpful to have the licenses (of coarse as open as possible) stored in close association with the data.</p>"
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 19
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [SimpleOption "No", SimpleOption "Yes"]
                                                              }
                                                            ]
                                                        }
                                                      ]
                                                  }
                                                ]
                                            ]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 21
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel = Just "How will you keep provenance?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription =
                                                Just
                                                  "<p class=\"question-description\">To make your experiments reproducible, all steps in the data processing must be documented in detail. The software you used, including version number, all options and parameters. This information together for every step of the analysis is part of the so-called data provenance. There are more questions regarding this in the chapter on data processing and curation.</p>"
                                            , chapterId = Just 2
                                            , questionId = Just 21
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions =
                                            [ SimpleOption
                                                "All steps will be documented in an (electronic) lab notebook"
                                            , SimpleOption
                                                "Our work flow system documents the provenance automatically and completely"
                                            ]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 22
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel = Just "How will you do file naming and file organization?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription =
                                                Just
                                                  "<p class=\"question-description\">Putting some thoughts into file naming can save a lot of trouble later.</p>"
                                            , chapterId = Just 2
                                            , questionId = Just 22
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions =
                                            [ SimpleOption "Skip"
                                            , DetailedOption
                                                NoNumbering
                                                "Explore"
                                                [ SimpleGroup
                                                  { sgDescriptor =
                                                      FIDescriptor
                                                      { iLabel = Nothing
                                                      , iNumbering = NoNumbering
                                                      , iIdent = Nothing
                                                      , iTags = []
                                                      , iShortDescription = Nothing
                                                      , iLongDescription = Nothing
                                                      , chapterId = Just 2
                                                      , questionId = Just 22
                                                      , iLink = Nothing
                                                      , iMandatory = True
                                                      , iRules = []
                                                      , iAutoComplete = []
                                                      }
                                                  , sgLevel = 0
                                                  , sgItems =
                                                      [ SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 23
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "Did you make a SOP (Standard Operating Procedure) for file naming?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription =
                                                                      Just
                                                                        "<p class=\"question-description\">It can help if everyone in the project uses the same naming scheme.</p>"
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 23
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [SimpleOption "No", SimpleOption "Yes"]
                                                              }
                                                            ]
                                                        }
                                                      , SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 24
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "Will you be keeping the relationships between data clear in the file names?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription =
                                                                      Just
                                                                        "<p class=\"question-description\">Advice: Use the same identifiers for sample IDs etc throughout the entire project.</p>"
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 24
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [SimpleOption "No", SimpleOption "Yes"]
                                                              }
                                                            ]
                                                        }
                                                      , SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 25
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "Will all the metadata in the file names also be available in the proper metadata?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription =
                                                                      Just
                                                                        "<p class=\"question-description\">The file names are very useful as metadata for people involved in the project, but to computers they are just identifiers. To prevent accidents with e.g. renamed files metadata information should always also be available elsewhere and not only through the file name.</p>"
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 25
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [ SimpleOption
                                                                      "No, the file names in the project are an essential part of the metadata"
                                                                  , SimpleOption
                                                                      "Yes, all metadata is also explicitly available elsewhere"
                                                                  ]
                                                              }
                                                            ]
                                                        }
                                                      ]
                                                  }
                                                ]
                                            ]
                                        }
                                      ]
                                  }
                                ]
                            }
                          ]
                      ]
                  }
                ]
            }
          , SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 2
                , questionId = Just 5
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "Is the risk of information loss, leaks and vandalism acceptably low?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription =
                          Just
                            "<p class=\"question-description\">There are many factors that can contribute to the risk of information loss or information leaks. They are often part of the behavior of the people that are involved in the project, but can also be steered by properly planned infrastructure.</p>"
                      , chapterId = Just 2
                      , questionId = Just 5
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions =
                      [ SimpleOption "Skip"
                      , DetailedOption
                          NoNumbering
                          "Explore"
                          [ SimpleGroup
                            { sgDescriptor =
                                FIDescriptor
                                { iLabel = Nothing
                                , iNumbering = NoNumbering
                                , iIdent = Nothing
                                , iTags = []
                                , iShortDescription = Nothing
                                , iLongDescription = Nothing
                                , chapterId = Just 2
                                , questionId = Just 5
                                , iLink = Nothing
                                , iMandatory = True
                                , iRules = []
                                , iAutoComplete = []
                                }
                            , sgLevel = 0
                            , sgItems =
                                [ SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 74
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel =
                                                Just
                                                  "Do project members store data or software on computers in the lab or external hard drives connected to those computers?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription =
                                                Just
                                                  "<p class=\"question-description\">When assessing the risk, take into account who has access to the lab, who has (physical) access to the computer hardware itself. Also consider whether data on those systems is properly backed up</p>"
                                            , chapterId = Just 2
                                            , questionId = Just 74
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions = [SimpleOption "No", SimpleOption "Yes"]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 75
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel = Just "Do project members carry data with them?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription =
                                                Just
                                                  "<p class=\"question-description\">Does anyone carry project data on laptops, USB sticks or other external media?</p>"
                                            , chapterId = Just 2
                                            , questionId = Just 75
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions =
                                            [ SimpleOption "No"
                                            , DetailedOption
                                                NoNumbering
                                                "Yes"
                                                [ SimpleGroup
                                                  { sgDescriptor =
                                                      FIDescriptor
                                                      { iLabel = Nothing
                                                      , iNumbering = NoNumbering
                                                      , iIdent = Nothing
                                                      , iTags = []
                                                      , iShortDescription = Nothing
                                                      , iLongDescription = Nothing
                                                      , chapterId = Just 2
                                                      , questionId = Just 75
                                                      , iLink = Nothing
                                                      , iMandatory = True
                                                      , iRules = []
                                                      , iAutoComplete = []
                                                      }
                                                  , sgLevel = 0
                                                  , sgItems =
                                                      [ SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 76
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "Are all data carriers encrypted? Are accounts on the laptop password protected?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription = Nothing
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 76
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [SimpleOption "No", SimpleOption "Yes"]
                                                              }
                                                            ]
                                                        }
                                                      ]
                                                  }
                                                ]
                                            ]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 77
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel = Just "Do project members store project data in cloud accounts?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription =
                                                Just
                                                  "<p class=\"question-description\">Think about services like Dropbox, but also about Google Drive, Apple iCloud accounts, or Microsoft's Office365</p>"
                                            , chapterId = Just 2
                                            , questionId = Just 77
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions = [SimpleOption "No", SimpleOption "Yes"]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 78
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel =
                                                Just
                                                  "Do project members send project data or reports per e-mail or other messaging services?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription = Nothing
                                            , chapterId = Just 2
                                            , questionId = Just 78
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions = [SimpleOption "No", SimpleOption "Yes"]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 79
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel =
                                                Just
                                                  "Do all data centers where project data is stored carry sufficient certifications?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription = Nothing
                                            , chapterId = Just 2
                                            , questionId = Just 79
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions = [SimpleOption "No", SimpleOption "Yes"]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 80
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel =
                                                Just
                                                  "Are all project web services addressed via secure http (https://)?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription = Nothing
                                            , chapterId = Just 2
                                            , questionId = Just 80
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions = [SimpleOption "No", SimpleOption "Yes"]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 81
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel =
                                                Just
                                                  "Have project members been instructed about the risks (generic and specific to the project)?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription =
                                                Just
                                                  "<p class=\"question-description\">Project members may need to know about passwords (not sharing accounts, using different passwords for each service, and two factor authentication), about security for data they carry (encryption, backups), data stored in their own labs and in personal cloud accounts, and about the use of open WiFi and https</p>"
                                            , chapterId = Just 2
                                            , questionId = Just 81
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions = [SimpleOption "No", SimpleOption "Yes"]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 82
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel =
                                                Just
                                                  "Did you consider the possible impact to the project or organization if information is lost?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription = Nothing
                                            , chapterId = Just 2
                                            , questionId = Just 82
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions =
                                            [ SimpleOption "No"
                                            , SimpleOption "The effect is small"
                                            , SimpleOption "The risk is acceptably low"
                                            ]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 83
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel =
                                                Just
                                                  "Did you consider the possible impact to the project or organization if information leaks?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription = Nothing
                                            , chapterId = Just 2
                                            , questionId = Just 83
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions =
                                            [ SimpleOption "No"
                                            , SimpleOption "The effect is small"
                                            , SimpleOption "The risk is acceptably low"
                                            ]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 84
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel =
                                                Just
                                                  "Did you consider the possible impact to the project or organization if information is vandalized?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription = Nothing
                                            , chapterId = Just 2
                                            , questionId = Just 84
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions =
                                            [ SimpleOption "No"
                                            , SimpleOption "The effect is small"
                                            , SimpleOption "The risk is acceptably low"
                                            ]
                                        }
                                      ]
                                  }
                                ]
                            }
                          ]
                      ]
                  }
                ]
            }
          , SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 2
                , questionId = Just 6
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "Do you need to do compute capacity planning?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription =
                          Just
                            "<p class=\"question-description\">If you require substantial amounts of compute power, amounts that are not trivially absorbed in what you usually have abailable, some planning is necessary. Do you think you need to do compute capacity planning?</p>"
                      , chapterId = Just 2
                      , questionId = Just 6
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions =
                      [ SimpleOption "No"
                      , DetailedOption
                          NoNumbering
                          "Yes"
                          [ SimpleGroup
                            { sgDescriptor =
                                FIDescriptor
                                { iLabel = Nothing
                                , iNumbering = NoNumbering
                                , iIdent = Nothing
                                , iTags = []
                                , iShortDescription = Nothing
                                , iLongDescription = Nothing
                                , chapterId = Just 2
                                , questionId = Just 6
                                , iLink = Nothing
                                , iMandatory = True
                                , iRules = []
                                , iAutoComplete = []
                                }
                            , sgLevel = 0
                            , sgItems =
                                [ SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 85
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel =
                                                Just
                                                  "Do you know how much CPU power, memory and I/O band width a typical analysis will take?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription =
                                                Just
                                                  "<p class=\"question-description\">Did you run pilot jobs? Do you know this information from comparable projects? Did you test whether the work scales up as you expected if you run more than one job?</p>"
                                            , chapterId = Just 2
                                            , questionId = Just 85
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions = [SimpleOption "No", SimpleOption "Yes"]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 86
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel =
                                                Just
                                                  "What type of compute architecture is most suitable for your work? Will you have that available?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription = Nothing
                                            , chapterId = Just 2
                                            , questionId = Just 86
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions =
                                            [ SimpleOption "We will use a compute cluster"
                                            , SimpleOption "We will use grid computing"
                                            , SimpleOption "We will use cloud computing"
                                            , SimpleOption
                                                "We will use a mix of computing architectures for different parts of the work"
                                            ]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 87
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel =
                                                Just
                                                  "Have you established with the provider when will you need the compute capacity?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription =
                                                Just
                                                  "<p class=\"question-description\">Do you need the compute capacity also for development? Can you start developing locally and start with a deployment test later?</p>"
                                            , chapterId = Just 2
                                            , questionId = Just 87
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions = [SimpleOption "No", SimpleOption "Yes"]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 88
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel =
                                                Just
                                                  "Is all required compute capacity available close to the project working storage area?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription = Nothing
                                            , chapterId = Just 2
                                            , questionId = Just 88
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions =
                                            [ DetailedOption
                                                NoNumbering
                                                "No"
                                                [ SimpleGroup
                                                  { sgDescriptor =
                                                      FIDescriptor
                                                      { iLabel = Nothing
                                                      , iNumbering = NoNumbering
                                                      , iIdent = Nothing
                                                      , iTags = []
                                                      , iShortDescription = Nothing
                                                      , iLongDescription = Nothing
                                                      , chapterId = Just 2
                                                      , questionId = Just 88
                                                      , iLink = Nothing
                                                      , iMandatory = True
                                                      , iRules = []
                                                      , iAutoComplete = []
                                                      }
                                                  , sgLevel = 0
                                                  , sgItems =
                                                      [ SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 89
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "Did you plan the required network capacity between storage and compute services?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription = Nothing
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 89
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [ SimpleOption
                                                                      "There are no special networking requirements"
                                                                  , SimpleOption
                                                                      "Copying or network delays are considered to be acceptable"
                                                                  , SimpleOption
                                                                      "We will be able to use a dedicated network connection"
                                                                  ]
                                                              }
                                                            ]
                                                        }
                                                      , SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 90
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "Can all data be legally transported and processed at the computing site?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription =
                                                                      Just
                                                                        "<p class=\"question-description\">Are the risks of data leaks covered?</p>"
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 90
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [SimpleOption "No", SimpleOption "Yes"]
                                                              }
                                                            ]
                                                        }
                                                      ]
                                                  }
                                                ]
                                            , SimpleOption "Yes"
                                            ]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 91
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel =
                                                Just
                                                  "Will different groups work on different parts of the workflow? Will parts of the computing be done on 'local' infrastructure to the group?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription = Nothing
                                            , chapterId = Just 2
                                            , questionId = Just 91
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions =
                                            [ SimpleOption
                                                "All steps of the workflow will be performed at central computing locations"
                                            , DetailedOption
                                                NoNumbering
                                                "Some steps may be performed at local computing locations"
                                                [ SimpleGroup
                                                  { sgDescriptor =
                                                      FIDescriptor
                                                      { iLabel = Nothing
                                                      , iNumbering = NoNumbering
                                                      , iIdent = Nothing
                                                      , iTags = []
                                                      , iShortDescription = Nothing
                                                      , iLongDescription = Nothing
                                                      , chapterId = Just 2
                                                      , questionId = Just 91
                                                      , iLink = Nothing
                                                      , iMandatory = True
                                                      , iRules = []
                                                      , iAutoComplete = []
                                                      }
                                                  , sgLevel = 0
                                                  , sgItems =
                                                      [ SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 92
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "Is there sufficient network capacity to the other computing locations?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription = Nothing
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 92
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [SimpleOption "No", SimpleOption "Yes"]
                                                              }
                                                            ]
                                                        }
                                                      ]
                                                  }
                                                ]
                                            ]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 93
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel =
                                                Just
                                                  "Is there sufficient experience with the chosen computer experience in the project?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription = Nothing
                                            , chapterId = Just 2
                                            , questionId = Just 93
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions =
                                            [ SimpleOption "We will recruit"
                                            , SimpleOption "Training has been arranged"
                                            , SimpleOption "Our people will be able to call for help"
                                            , SimpleOption "We have sufficient knowledge in the project"
                                            ]
                                        }
                                      ]
                                  }
                                ]
                            }
                          ]
                      ]
                  }
                ]
            }
          , SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 2
                , questionId = Just 26
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "Will you be archiving data for long term preservation?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , chapterId = Just 2
                      , questionId = Just 26
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions =
                      [ DetailedOption
                          NoNumbering
                          "No"
                          [ SimpleGroup
                            { sgDescriptor =
                                FIDescriptor
                                { iLabel = Nothing
                                , iNumbering = NoNumbering
                                , iIdent = Nothing
                                , iTags = []
                                , iShortDescription = Nothing
                                , iLongDescription = Nothing
                                , chapterId = Just 2
                                , questionId = Just 26
                                , iLink = Nothing
                                , iMandatory = True
                                , iRules = []
                                , iAutoComplete = []
                                }
                            , sgLevel = 0
                            , sgItems =
                                [ SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 27
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel = Just "Can the original data be recreated?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription = Nothing
                                            , chapterId = Just 2
                                            , questionId = Just 27
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions = [SimpleOption "No", SimpleOption "Yes"]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 30
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel = Just "When is the raw data archived?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription = Nothing
                                            , chapterId = Just 2
                                            , questionId = Just 30
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions =
                                            [ SimpleOption "As soon as it comes in, in chunks"
                                            , SimpleOption "As soon as it has all arrived, in one session"
                                            , SimpleOption "All at once with the results at the end of the project"
                                            ]
                                        }
                                      ]
                                  }
                                ]
                            }
                          ]
                      , DetailedOption
                          NoNumbering
                          "Yes"
                          [ SimpleGroup
                            { sgDescriptor =
                                FIDescriptor
                                { iLabel = Nothing
                                , iNumbering = NoNumbering
                                , iIdent = Nothing
                                , iTags = []
                                , iShortDescription = Nothing
                                , iLongDescription = Nothing
                                , chapterId = Just 2
                                , questionId = Just 26
                                , iLink = Nothing
                                , iMandatory = True
                                , iRules = []
                                , iAutoComplete = []
                                }
                            , sgLevel = 0
                            , sgItems =
                                [ SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 28
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel =
                                                Just "Is the archived data changing over time, needing re-archival?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription = Nothing
                                            , chapterId = Just 2
                                            , questionId = Just 28
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions =
                                            [ SimpleOption "No"
                                            , DetailedOption
                                                NoNumbering
                                                "Yes"
                                                [ SimpleGroup
                                                  { sgDescriptor =
                                                      FIDescriptor
                                                      { iLabel = Nothing
                                                      , iNumbering = NoNumbering
                                                      , iIdent = Nothing
                                                      , iTags = []
                                                      , iShortDescription = Nothing
                                                      , iLongDescription = Nothing
                                                      , chapterId = Just 2
                                                      , questionId = Just 28
                                                      , iLink = Nothing
                                                      , iMandatory = True
                                                      , iRules = []
                                                      , iAutoComplete = []
                                                      }
                                                  , sgLevel = 0
                                                  , sgItems =
                                                      [ SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 29
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel = Just "Do you need frequent backups?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription = Nothing
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 29
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [ SimpleOption "No, data changes infrequently"
                                                                  , SimpleOption "Yes, data changes frequently"
                                                                  ]
                                                              }
                                                            ]
                                                        }
                                                      , SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 31
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "Will you be relying on these backups to recover from human error (accidental changes or deletions)?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription = Nothing
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 31
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [SimpleOption "No", SimpleOption "Yes"]
                                                              }
                                                            ]
                                                        }
                                                      ]
                                                  }
                                                ]
                                            ]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 32
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel = Just "Will the archive be stored on disc or on tape?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription = Nothing
                                            , chapterId = Just 2
                                            , questionId = Just 32
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions = [SimpleOption "Disc", SimpleOption "Tape"]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 33
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel =
                                                Just
                                                  "Will the archive be stored in a remote location, protecting the data against disasters?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription = Nothing
                                            , chapterId = Just 2
                                            , questionId = Just 33
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions = [SimpleOption "No", SimpleOption "Yes"]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 34
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel =
                                                Just "Will the archive need to be protected against loss or theft?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription = Nothing
                                            , chapterId = Just 2
                                            , questionId = Just 34
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions =
                                            [ SimpleOption "No"
                                            , DetailedOption
                                                NoNumbering
                                                "Yes"
                                                [ SimpleGroup
                                                  { sgDescriptor =
                                                      FIDescriptor
                                                      { iLabel = Nothing
                                                      , iNumbering = NoNumbering
                                                      , iIdent = Nothing
                                                      , iTags = []
                                                      , iShortDescription = Nothing
                                                      , iLongDescription = Nothing
                                                      , chapterId = Just 2
                                                      , questionId = Just 34
                                                      , iLink = Nothing
                                                      , iMandatory = True
                                                      , iRules = []
                                                      , iAutoComplete = []
                                                      }
                                                  , sgLevel = 0
                                                  , sgItems =
                                                      [ SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 35
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel = Just "Will the archive be encrypted?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription = Nothing
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 35
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [ SimpleOption "No"
                                                                  , DetailedOption
                                                                      NoNumbering
                                                                      "Yes"
                                                                      [ SimpleGroup
                                                                        { sgDescriptor =
                                                                            FIDescriptor
                                                                            { iLabel = Nothing
                                                                            , iNumbering = NoNumbering
                                                                            , iIdent = Nothing
                                                                            , iTags = []
                                                                            , iShortDescription = Nothing
                                                                            , iLongDescription = Nothing
                                                                            , chapterId = Just 2
                                                                            , questionId = Just 35
                                                                            , iLink = Nothing
                                                                            , iMandatory = True
                                                                            , iRules = []
                                                                            , iAutoComplete = []
                                                                            }
                                                                        , sgLevel = 0
                                                                        , sgItems =
                                                                            [ SimpleGroup
                                                                              { sgDescriptor =
                                                                                  FIDescriptor
                                                                                  { iLabel = Nothing
                                                                                  , iNumbering = NoNumbering
                                                                                  , iIdent = Nothing
                                                                                  , iTags = []
                                                                                  , iShortDescription = Nothing
                                                                                  , iLongDescription = Nothing
                                                                                  , chapterId = Just 2
                                                                                  , questionId = Just 36
                                                                                  , iLink = Nothing
                                                                                  , iMandatory = False
                                                                                  , iRules = []
                                                                                  , iAutoComplete = []
                                                                                  }
                                                                              , sgLevel = 0
                                                                              , sgItems =
                                                                                  [ ChoiceFI
                                                                                    { chfiDescriptor =
                                                                                        FIDescriptor
                                                                                        { iLabel =
                                                                                            Just
                                                                                              "Is it clear who has access to the key? Also in case of a required data restore?"
                                                                                        , iNumbering = NoNumbering
                                                                                        , iIdent = Nothing
                                                                                        , iTags = []
                                                                                        , iShortDescription = Nothing
                                                                                        , iLongDescription = Nothing
                                                                                        , chapterId = Just 2
                                                                                        , questionId = Just 36
                                                                                        , iLink = Nothing
                                                                                        , iMandatory = True
                                                                                        , iRules = []
                                                                                        , iAutoComplete = []
                                                                                        }
                                                                                    , chfiAvailableOptions =
                                                                                        [ SimpleOption "No"
                                                                                        , SimpleOption "Yes"
                                                                                        ]
                                                                                    }
                                                                                  ]
                                                                              }
                                                                            ]
                                                                        }
                                                                      ]
                                                                  ]
                                                              }
                                                            ]
                                                        }
                                                      , SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 37
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "Is it clear who has physical access to the archives?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription = Nothing
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 37
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [SimpleOption "No", SimpleOption "Yes"]
                                                              }
                                                            ]
                                                        }
                                                      ]
                                                  }
                                                ]
                                            ]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 38
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel =
                                                Just "Will your project require the archives to be available on-line?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription = Nothing
                                            , chapterId = Just 2
                                            , questionId = Just 38
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions =
                                            [ SimpleOption "No"
                                            , DetailedOption
                                                NoNumbering
                                                "Yes"
                                                [ SimpleGroup
                                                  { sgDescriptor =
                                                      FIDescriptor
                                                      { iLabel = Nothing
                                                      , iNumbering = NoNumbering
                                                      , iIdent = Nothing
                                                      , iTags = []
                                                      , iShortDescription = Nothing
                                                      , iLongDescription = Nothing
                                                      , chapterId = Just 2
                                                      , questionId = Just 38
                                                      , iLink = Nothing
                                                      , iMandatory = True
                                                      , iRules = []
                                                      , iAutoComplete = []
                                                      }
                                                  , sgLevel = 0
                                                  , sgItems =
                                                      [ SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 39
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel = Just "Will data integrity be guaranteed?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription =
                                                                      Just
                                                                        "<p class=\"question-description\">If the 'master copy' of the data is available on line, it should probably be protected against being tampered with.</p>"
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 39
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [SimpleOption "No", SimpleOption "Yes"]
                                                              }
                                                            ]
                                                        }
                                                      ]
                                                  }
                                                ]
                                            ]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 40
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel =
                                                Just
                                                  "Has it been established who has access to the archive, and how fast?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription = Nothing
                                            , chapterId = Just 2
                                            , questionId = Just 40
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions =
                                            [ SimpleOption "No"
                                            , DetailedOption
                                                NoNumbering
                                                "Yes"
                                                [ SimpleGroup
                                                  { sgDescriptor =
                                                      FIDescriptor
                                                      { iLabel = Nothing
                                                      , iNumbering = NoNumbering
                                                      , iIdent = Nothing
                                                      , iTags = []
                                                      , iShortDescription = Nothing
                                                      , iLongDescription = Nothing
                                                      , chapterId = Just 2
                                                      , questionId = Just 40
                                                      , iLink = Nothing
                                                      , iMandatory = True
                                                      , iRules = []
                                                      , iAutoComplete = []
                                                      }
                                                  , sgLevel = 0
                                                  , sgItems =
                                                      [ SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 41
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "Has it been established who can ask for a restore during the project?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription = Nothing
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 41
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [SimpleOption "No", SimpleOption "Yes"]
                                                              }
                                                            ]
                                                        }
                                                      , SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 42
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "If the data is voluminous, will the project be able to cope with the time needed for a restore?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription = Nothing
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 42
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [SimpleOption "No", SimpleOption "Yes"]
                                                              }
                                                            ]
                                                        }
                                                      , SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 43
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "has authority over the data been arranged for when the project is finished (potentially long ago)? Is there a data access committee?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription = Nothing
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 43
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [SimpleOption "No", SimpleOption "Yes"]
                                                              }
                                                            ]
                                                        }
                                                      ]
                                                  }
                                                ]
                                            ]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 44
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel =
                                                Just
                                                  "Has it been established how long the archived data need to be kept? For each of the different parts of the archive (raw data / results)?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription = Nothing
                                            , chapterId = Just 2
                                            , questionId = Just 44
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions = [SimpleOption "No", SimpleOption "Yes"]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 45
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel = Just "Will the data still be understandable after a long time?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription =
                                                Just
                                                  "<p class=\"question-description\">See also all questions about keeping metadata and data formats. Make sure the metadata is kept close to the data in the archive, and that community supported data formats are used for all long term archiving.</p>"
                                            , chapterId = Just 2
                                            , questionId = Just 45
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions = [SimpleOption "No", SimpleOption "Yes"]
                                        }
                                      ]
                                  }
                                ]
                            }
                          ]
                      ]
                  }
                ]
            }
          , SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 2
                , questionId = Just 46
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "Will you need a shared working space to work with your data?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , chapterId = Just 2
                      , questionId = Just 46
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions =
                      [ DetailedOption
                          NoNumbering
                          "No"
                          [ SimpleGroup
                            { sgDescriptor =
                                FIDescriptor
                                { iLabel = Nothing
                                , iNumbering = NoNumbering
                                , iIdent = Nothing
                                , iTags = []
                                , iShortDescription = Nothing
                                , iLongDescription = Nothing
                                , chapterId = Just 2
                                , questionId = Just 46
                                , iLink = Nothing
                                , iMandatory = True
                                , iRules = []
                                , iAutoComplete = []
                                }
                            , sgLevel = 0
                            , sgItems =
                                [ SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 73
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel =
                                                Just
                                                  "Are data all project members store adequately backed up and traceable?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription = Nothing
                                            , chapterId = Just 2
                                            , questionId = Just 73
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions =
                                            [ SimpleOption "No"
                                            , SimpleOption
                                                "Yes, protected against both equipment failure and human error"
                                            ]
                                        }
                                      ]
                                  }
                                ]
                            }
                          ]
                      , DetailedOption
                          NoNumbering
                          "Yes"
                          [ SimpleGroup
                            { sgDescriptor =
                                FIDescriptor
                                { iLabel = Nothing
                                , iNumbering = NoNumbering
                                , iIdent = Nothing
                                , iTags = []
                                , iShortDescription = Nothing
                                , iLongDescription = Nothing
                                , chapterId = Just 2
                                , questionId = Just 46
                                , iLink = Nothing
                                , iMandatory = True
                                , iRules = []
                                , iAutoComplete = []
                                }
                            , sgLevel = 0
                            , sgItems =
                                [ SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 47
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel = Just "How will you work with your data?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription = Nothing
                                            , chapterId = Just 2
                                            , questionId = Just 47
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions =
                                            [ SimpleOption "Skip"
                                            , DetailedOption
                                                NoNumbering
                                                "Explore"
                                                [ SimpleGroup
                                                  { sgDescriptor =
                                                      FIDescriptor
                                                      { iLabel = Nothing
                                                      , iNumbering = NoNumbering
                                                      , iIdent = Nothing
                                                      , iTags = []
                                                      , iShortDescription = Nothing
                                                      , iLongDescription = Nothing
                                                      , chapterId = Just 2
                                                      , questionId = Just 47
                                                      , iLink = Nothing
                                                      , iMandatory = True
                                                      , iRules = []
                                                      , iAutoComplete = []
                                                      }
                                                  , sgLevel = 0
                                                  , sgItems =
                                                      [ SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 48
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ TextFI
                                                              { tfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "What kind of data will you have in your work space?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription =
                                                                      Just
                                                                        "When making the work space, it helps to know whether you expect to work with very many small files, a few very large files, whether you will use a (SQL) database to store most of the data. Maybe your data is suitable for a system like Hadoop? Such information can be collected here."
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 48
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              }
                                                            ]
                                                        }
                                                      , SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 49
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "Do you need the work space to be close to the compute capacity?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription =
                                                                      Just
                                                                        "<p class=\"question-description\">If you have large volumes of data that are intensely and repeatedly used by the computing work flow, it may be needed to keep the storage in the same place as where the computing takes place.</p>"
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 49
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [SimpleOption "No", SimpleOption "Yes"]
                                                              }
                                                            ]
                                                        }
                                                      , SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 50
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "Will you be working with your data in another form than the way it will be archived?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription =
                                                                      Just
                                                                        "<p class=\"question-description\">Archival and working with data have different requirements. You want archived information to be in a form that others could read and in a format that is also understandable in a number of years. When working with the data, you need to be able to address it efficiently. If the two differ, you need to plan for conversions.</p>"
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 50
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [ SimpleOption
                                                                      "No, data format will be archived in the same way we work with it"
                                                                  , SimpleOption
                                                                      "Yes, archival will require a conversion step"
                                                                  ]
                                                              }
                                                            ]
                                                        }
                                                      , SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 51
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just "How does the storage need change over time?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription =
                                                                      Just
                                                                        "<p class=\"question-description\">To perform capacity planning, it is important to know what the need for storage capacity at the beginning and the end of the project will be.</p>"
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 51
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [ SimpleOption
                                                                      "Storage needs will be the same during the whole project"
                                                                  , SimpleOption
                                                                      "Storage needs are large at the beginning and will be reduced later"
                                                                  , SimpleOption
                                                                      "Storage needs are small at the beginning and will grow later"
                                                                  , SimpleOption
                                                                      "Storage needs are largest in the middle of the project"
                                                                  , DetailedOption
                                                                      NoNumbering
                                                                      "Explore"
                                                                      [ SimpleGroup
                                                                        { sgDescriptor =
                                                                            FIDescriptor
                                                                            { iLabel = Nothing
                                                                            , iNumbering = NoNumbering
                                                                            , iIdent = Nothing
                                                                            , iTags = []
                                                                            , iShortDescription = Nothing
                                                                            , iLongDescription = Nothing
                                                                            , chapterId = Just 2
                                                                            , questionId = Just 51
                                                                            , iLink = Nothing
                                                                            , iMandatory = True
                                                                            , iRules = []
                                                                            , iAutoComplete = []
                                                                            }
                                                                        , sgLevel = 0
                                                                        , sgItems =
                                                                            [ SimpleGroup
                                                                              { sgDescriptor =
                                                                                  FIDescriptor
                                                                                  { iLabel = Nothing
                                                                                  , iNumbering = NoNumbering
                                                                                  , iIdent = Nothing
                                                                                  , iTags = []
                                                                                  , iShortDescription = Nothing
                                                                                  , iLongDescription = Nothing
                                                                                  , chapterId = Just 2
                                                                                  , questionId = Just 52
                                                                                  , iLink = Nothing
                                                                                  , iMandatory = False
                                                                                  , iRules = []
                                                                                  , iAutoComplete = []
                                                                                  }
                                                                              , sgLevel = 0
                                                                              , sgItems =
                                                                                  [ ChoiceFI
                                                                                    { chfiDescriptor =
                                                                                        FIDescriptor
                                                                                        { iLabel =
                                                                                            Just
                                                                                              "When will your raw data become available?"
                                                                                        , iNumbering = NoNumbering
                                                                                        , iIdent = Nothing
                                                                                        , iTags = []
                                                                                        , iShortDescription = Nothing
                                                                                        , iLongDescription = Nothing
                                                                                        , chapterId = Just 2
                                                                                        , questionId = Just 52
                                                                                        , iLink = Nothing
                                                                                        , iMandatory = True
                                                                                        , iRules = []
                                                                                        , iAutoComplete = []
                                                                                        }
                                                                                    , chfiAvailableOptions =
                                                                                        [ SimpleOption
                                                                                            "Raw data will come in right at the start"
                                                                                        , SimpleOption
                                                                                            "Raw data will come in during the project"
                                                                                        ]
                                                                                    }
                                                                                  ]
                                                                              }
                                                                            , SimpleGroup
                                                                              { sgDescriptor =
                                                                                  FIDescriptor
                                                                                  { iLabel = Nothing
                                                                                  , iNumbering = NoNumbering
                                                                                  , iIdent = Nothing
                                                                                  , iTags = []
                                                                                  , iShortDescription = Nothing
                                                                                  , iLongDescription = Nothing
                                                                                  , chapterId = Just 2
                                                                                  , questionId = Just 53
                                                                                  , iLink = Nothing
                                                                                  , iMandatory = False
                                                                                  , iRules = []
                                                                                  , iAutoComplete = []
                                                                                  }
                                                                              , sgLevel = 0
                                                                              , sgItems =
                                                                                  [ ChoiceFI
                                                                                    { chfiDescriptor =
                                                                                        FIDescriptor
                                                                                        { iLabel =
                                                                                            Just
                                                                                              "How much of the raw data do you need to keep in the work space?"
                                                                                        , iNumbering = NoNumbering
                                                                                        , iIdent = Nothing
                                                                                        , iTags = []
                                                                                        , iShortDescription = Nothing
                                                                                        , iLongDescription =
                                                                                            Just
                                                                                              "<p class=\"question-description\">Sometimes the raw data is relatively large, and it pays of to clean it quickly.</p>"
                                                                                        , chapterId = Just 2
                                                                                        , questionId = Just 53
                                                                                        , iLink = Nothing
                                                                                        , iMandatory = True
                                                                                        , iRules = []
                                                                                        , iAutoComplete = []
                                                                                        }
                                                                                    , chfiAvailableOptions =
                                                                                        [ SimpleOption
                                                                                            "Raw data will need to stay in the work space"
                                                                                        , DetailedOption
                                                                                            NoNumbering
                                                                                            "Raw data can be cleaned out or archived quickly"
                                                                                            [ SimpleGroup
                                                                                              { sgDescriptor =
                                                                                                  FIDescriptor
                                                                                                  { iLabel = Nothing
                                                                                                  , iNumbering =
                                                                                                      NoNumbering
                                                                                                  , iIdent = Nothing
                                                                                                  , iTags = []
                                                                                                  , iShortDescription =
                                                                                                      Nothing
                                                                                                  , iLongDescription =
                                                                                                      Nothing
                                                                                                  , chapterId = Just 2
                                                                                                  , questionId = Just 53
                                                                                                  , iLink = Nothing
                                                                                                  , iMandatory = True
                                                                                                  , iRules = []
                                                                                                  , iAutoComplete = []
                                                                                                  }
                                                                                              , sgLevel = 0
                                                                                              , sgItems =
                                                                                                  [ SimpleGroup
                                                                                                    { sgDescriptor =
                                                                                                        FIDescriptor
                                                                                                        { iLabel =
                                                                                                            Nothing
                                                                                                        , iNumbering =
                                                                                                            NoNumbering
                                                                                                        , iIdent =
                                                                                                            Nothing
                                                                                                        , iTags = []
                                                                                                        , iShortDescription =
                                                                                                            Nothing
                                                                                                        , iLongDescription =
                                                                                                            Nothing
                                                                                                        , chapterId =
                                                                                                            Just 2
                                                                                                        , questionId =
                                                                                                            Just 54
                                                                                                        , iLink =
                                                                                                            Nothing
                                                                                                        , iMandatory =
                                                                                                            False
                                                                                                        , iRules = []
                                                                                                        , iAutoComplete =
                                                                                                            []
                                                                                                        }
                                                                                                    , sgLevel = 0
                                                                                                    , sgItems =
                                                                                                        [ ChoiceFI
                                                                                                          { chfiDescriptor =
                                                                                                              FIDescriptor
                                                                                                              { iLabel =
                                                                                                                  Just
                                                                                                                    "Do your raw data need to be archived?"
                                                                                                              , iNumbering =
                                                                                                                  NoNumbering
                                                                                                              , iIdent =
                                                                                                                  Nothing
                                                                                                              , iTags =
                                                                                                                  []
                                                                                                              , iShortDescription =
                                                                                                                  Nothing
                                                                                                              , iLongDescription =
                                                                                                                  Nothing
                                                                                                              , chapterId =
                                                                                                                  Just 2
                                                                                                              , questionId =
                                                                                                                  Just
                                                                                                                    54
                                                                                                              , iLink =
                                                                                                                  Nothing
                                                                                                              , iMandatory =
                                                                                                                  True
                                                                                                              , iRules =
                                                                                                                  []
                                                                                                              , iAutoComplete =
                                                                                                                  []
                                                                                                              }
                                                                                                          , chfiAvailableOptions =
                                                                                                              [ SimpleOption
                                                                                                                  "No, it is also stored elsewhere can can be recovered easily"
                                                                                                              , SimpleOption
                                                                                                                  "No, it can be remeasured easily and more cheaply than archiving"
                                                                                                              , SimpleOption
                                                                                                                  "Yes"
                                                                                                              ]
                                                                                                          }
                                                                                                        ]
                                                                                                    }
                                                                                                  ]
                                                                                              }
                                                                                            ]
                                                                                        , SimpleOption
                                                                                            "Raw data do not form a major part of the storage needs"
                                                                                        ]
                                                                                    }
                                                                                  ]
                                                                              }
                                                                            , SimpleGroup
                                                                              { sgDescriptor =
                                                                                  FIDescriptor
                                                                                  { iLabel = Nothing
                                                                                  , iNumbering = NoNumbering
                                                                                  , iIdent = Nothing
                                                                                  , iTags = []
                                                                                  , iShortDescription = Nothing
                                                                                  , iLongDescription = Nothing
                                                                                  , chapterId = Just 2
                                                                                  , questionId = Just 55
                                                                                  , iLink = Nothing
                                                                                  , iMandatory = False
                                                                                  , iRules = []
                                                                                  , iAutoComplete = []
                                                                                  }
                                                                              , sgLevel = 0
                                                                              , sgItems =
                                                                                  [ ChoiceFI
                                                                                    { chfiDescriptor =
                                                                                        FIDescriptor
                                                                                        { iLabel =
                                                                                            Just
                                                                                              "Did you plan how much intermediate data you will get during analysis and how long each step needs to be kept?"
                                                                                        , iNumbering = NoNumbering
                                                                                        , iIdent = Nothing
                                                                                        , iTags = []
                                                                                        , iShortDescription = Nothing
                                                                                        , iLongDescription = Nothing
                                                                                        , chapterId = Just 2
                                                                                        , questionId = Just 55
                                                                                        , iLink = Nothing
                                                                                        , iMandatory = True
                                                                                        , iRules = []
                                                                                        , iAutoComplete = []
                                                                                        }
                                                                                    , chfiAvailableOptions =
                                                                                        [ SimpleOption
                                                                                            "The volume of intermediate data will not be significant"
                                                                                        , DetailedOption
                                                                                            NoNumbering
                                                                                            "A large volume of intermediate data will be in the work space"
                                                                                            [ SimpleGroup
                                                                                              { sgDescriptor =
                                                                                                  FIDescriptor
                                                                                                  { iLabel = Nothing
                                                                                                  , iNumbering =
                                                                                                      NoNumbering
                                                                                                  , iIdent = Nothing
                                                                                                  , iTags = []
                                                                                                  , iShortDescription =
                                                                                                      Nothing
                                                                                                  , iLongDescription =
                                                                                                      Nothing
                                                                                                  , chapterId = Just 2
                                                                                                  , questionId = Just 55
                                                                                                  , iLink = Nothing
                                                                                                  , iMandatory = True
                                                                                                  , iRules = []
                                                                                                  , iAutoComplete = []
                                                                                                  }
                                                                                              , sgLevel = 0
                                                                                              , sgItems =
                                                                                                  [ SimpleGroup
                                                                                                    { sgDescriptor =
                                                                                                        FIDescriptor
                                                                                                        { iLabel =
                                                                                                            Nothing
                                                                                                        , iNumbering =
                                                                                                            NoNumbering
                                                                                                        , iIdent =
                                                                                                            Nothing
                                                                                                        , iTags = []
                                                                                                        , iShortDescription =
                                                                                                            Nothing
                                                                                                        , iLongDescription =
                                                                                                            Nothing
                                                                                                        , chapterId =
                                                                                                            Just 2
                                                                                                        , questionId =
                                                                                                            Just 56
                                                                                                        , iLink =
                                                                                                            Nothing
                                                                                                        , iMandatory =
                                                                                                            False
                                                                                                        , iRules = []
                                                                                                        , iAutoComplete =
                                                                                                            []
                                                                                                        }
                                                                                                    , sgLevel = 0
                                                                                                    , sgItems =
                                                                                                        [ ChoiceFI
                                                                                                          { chfiDescriptor =
                                                                                                              FIDescriptor
                                                                                                              { iLabel =
                                                                                                                  Just
                                                                                                                    "Is it possible to store intermediate temporary data on a separate (scratch) file system that is not backed up?"
                                                                                                              , iNumbering =
                                                                                                                  NoNumbering
                                                                                                              , iIdent =
                                                                                                                  Nothing
                                                                                                              , iTags =
                                                                                                                  []
                                                                                                              , iShortDescription =
                                                                                                                  Nothing
                                                                                                              , iLongDescription =
                                                                                                                  Just
                                                                                                                    "<p class=\"question-description\">If the intermediate results are in your main work space, a restore in case of a problem could take much more time. It may be faster to recover it by re-running computations</p>"
                                                                                                              , chapterId =
                                                                                                                  Just 2
                                                                                                              , questionId =
                                                                                                                  Just
                                                                                                                    56
                                                                                                              , iLink =
                                                                                                                  Nothing
                                                                                                              , iMandatory =
                                                                                                                  True
                                                                                                              , iRules =
                                                                                                                  []
                                                                                                              , iAutoComplete =
                                                                                                                  []
                                                                                                              }
                                                                                                          , chfiAvailableOptions =
                                                                                                              [ SimpleOption
                                                                                                                  "We will use the main work space for temporary data"
                                                                                                              , DetailedOption
                                                                                                                  NoNumbering
                                                                                                                  "We can offload intermediate results to a scratch file system that is not backed up"
                                                                                                                  [ SimpleGroup
                                                                                                                    { sgDescriptor =
                                                                                                                        FIDescriptor
                                                                                                                        { iLabel =
                                                                                                                            Nothing
                                                                                                                        , iNumbering =
                                                                                                                            NoNumbering
                                                                                                                        , iIdent =
                                                                                                                            Nothing
                                                                                                                        , iTags =
                                                                                                                            [
                                                                                                                            ]
                                                                                                                        , iShortDescription =
                                                                                                                            Nothing
                                                                                                                        , iLongDescription =
                                                                                                                            Nothing
                                                                                                                        , chapterId =
                                                                                                                            Just
                                                                                                                              2
                                                                                                                        , questionId =
                                                                                                                            Just
                                                                                                                              56
                                                                                                                        , iLink =
                                                                                                                            Nothing
                                                                                                                        , iMandatory =
                                                                                                                            True
                                                                                                                        , iRules =
                                                                                                                            [
                                                                                                                            ]
                                                                                                                        , iAutoComplete =
                                                                                                                            [
                                                                                                                            ]
                                                                                                                        }
                                                                                                                    , sgLevel =
                                                                                                                        0
                                                                                                                    , sgItems =
                                                                                                                        [ SimpleGroup
                                                                                                                          { sgDescriptor =
                                                                                                                              FIDescriptor
                                                                                                                              { iLabel =
                                                                                                                                  Nothing
                                                                                                                              , iNumbering =
                                                                                                                                  NoNumbering
                                                                                                                              , iIdent =
                                                                                                                                  Nothing
                                                                                                                              , iTags =
                                                                                                                                  [
                                                                                                                                  ]
                                                                                                                              , iShortDescription =
                                                                                                                                  Nothing
                                                                                                                              , iLongDescription =
                                                                                                                                  Nothing
                                                                                                                              , chapterId =
                                                                                                                                  Just
                                                                                                                                    2
                                                                                                                              , questionId =
                                                                                                                                  Just
                                                                                                                                    71
                                                                                                                              , iLink =
                                                                                                                                  Nothing
                                                                                                                              , iMandatory =
                                                                                                                                  False
                                                                                                                              , iRules =
                                                                                                                                  [
                                                                                                                                  ]
                                                                                                                              , iAutoComplete =
                                                                                                                                  [
                                                                                                                                  ]
                                                                                                                              }
                                                                                                                          , sgLevel =
                                                                                                                              0
                                                                                                                          , sgItems =
                                                                                                                              [ ChoiceFI
                                                                                                                                { chfiDescriptor =
                                                                                                                                    FIDescriptor
                                                                                                                                    { iLabel =
                                                                                                                                        Just
                                                                                                                                          "Are you sure you will not need a backup of the data stored on the scratch file systems (any scratch you use)?"
                                                                                                                                    , iNumbering =
                                                                                                                                        NoNumbering
                                                                                                                                    , iIdent =
                                                                                                                                        Nothing
                                                                                                                                    , iTags =
                                                                                                                                        [
                                                                                                                                        ]
                                                                                                                                    , iShortDescription =
                                                                                                                                        Nothing
                                                                                                                                    , iLongDescription =
                                                                                                                                        Nothing
                                                                                                                                    , chapterId =
                                                                                                                                        Just
                                                                                                                                          2
                                                                                                                                    , questionId =
                                                                                                                                        Just
                                                                                                                                          71
                                                                                                                                    , iLink =
                                                                                                                                        Nothing
                                                                                                                                    , iMandatory =
                                                                                                                                        True
                                                                                                                                    , iRules =
                                                                                                                                        [
                                                                                                                                        ]
                                                                                                                                    , iAutoComplete =
                                                                                                                                        [
                                                                                                                                        ]
                                                                                                                                    }
                                                                                                                                , chfiAvailableOptions =
                                                                                                                                    [ SimpleOption
                                                                                                                                        "No"
                                                                                                                                    , SimpleOption
                                                                                                                                        "Yes"
                                                                                                                                    ]
                                                                                                                                }
                                                                                                                              ]
                                                                                                                          }
                                                                                                                        ]
                                                                                                                    }
                                                                                                                  ]
                                                                                                              ]
                                                                                                          }
                                                                                                        ]
                                                                                                    }
                                                                                                  ]
                                                                                              }
                                                                                            ]
                                                                                        ]
                                                                                    }
                                                                                  ]
                                                                              }
                                                                            , SimpleGroup
                                                                              { sgDescriptor =
                                                                                  FIDescriptor
                                                                                  { iLabel = Nothing
                                                                                  , iNumbering = NoNumbering
                                                                                  , iIdent = Nothing
                                                                                  , iTags = []
                                                                                  , iShortDescription = Nothing
                                                                                  , iLongDescription = Nothing
                                                                                  , chapterId = Just 2
                                                                                  , questionId = Just 57
                                                                                  , iLink = Nothing
                                                                                  , iMandatory = False
                                                                                  , iRules = []
                                                                                  , iAutoComplete = []
                                                                                  }
                                                                              , sgLevel = 0
                                                                              , sgItems =
                                                                                  [ ChoiceFI
                                                                                    { chfiDescriptor =
                                                                                        FIDescriptor
                                                                                        { iLabel =
                                                                                            Just
                                                                                              "Will you have different versions of intermediate data that need to be kept?"
                                                                                        , iNumbering = NoNumbering
                                                                                        , iIdent = Nothing
                                                                                        , iTags = []
                                                                                        , iShortDescription = Nothing
                                                                                        , iLongDescription =
                                                                                            Just
                                                                                              "<p class=\"question-description\">Consider storing only the workflow parameters if the data itself could be reproduced quickly</p>"
                                                                                        , chapterId = Just 2
                                                                                        , questionId = Just 57
                                                                                        , iLink = Nothing
                                                                                        , iMandatory = True
                                                                                        , iRules = []
                                                                                        , iAutoComplete = []
                                                                                        }
                                                                                    , chfiAvailableOptions =
                                                                                        [ SimpleOption "No"
                                                                                        , SimpleOption "Yes"
                                                                                        ]
                                                                                    }
                                                                                  ]
                                                                              }
                                                                            ]
                                                                        }
                                                                      ]
                                                                  ]
                                                              }
                                                            ]
                                                        }
                                                      , SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 58
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "Will you need to temporarilty archive data sets (to tape)?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription = Nothing
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 58
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [SimpleOption "No", SimpleOption "Yes"]
                                                              }
                                                            ]
                                                        }
                                                      , SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 59
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel = Just "How will your first data come in?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription = Nothing
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 59
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [ SimpleOption
                                                                      "No special planning is needed for the initial data"
                                                                  , SimpleOption
                                                                      "Initial data will need to be made available through a local network copy"
                                                                  , SimpleOption
                                                                      "We will need a high-speed network connection to copy the initial data"
                                                                  , SimpleOption
                                                                      "Initial data will arrive on separate media and will need to be copied to the work space"
                                                                  ]
                                                              }
                                                            ]
                                                        }
                                                      , SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 60
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "How will project partners access the work space?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription = Nothing
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 60
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [ SimpleOption "Skip"
                                                                  , DetailedOption
                                                                      NoNumbering
                                                                      "Explore"
                                                                      [ SimpleGroup
                                                                        { sgDescriptor =
                                                                            FIDescriptor
                                                                            { iLabel = Nothing
                                                                            , iNumbering = NoNumbering
                                                                            , iIdent = Nothing
                                                                            , iTags = []
                                                                            , iShortDescription = Nothing
                                                                            , iLongDescription = Nothing
                                                                            , chapterId = Just 2
                                                                            , questionId = Just 60
                                                                            , iLink = Nothing
                                                                            , iMandatory = True
                                                                            , iRules = []
                                                                            , iAutoComplete = []
                                                                            }
                                                                        , sgLevel = 0
                                                                        , sgItems =
                                                                            [ SimpleGroup
                                                                              { sgDescriptor =
                                                                                  FIDescriptor
                                                                                  { iLabel = Nothing
                                                                                  , iNumbering = NoNumbering
                                                                                  , iIdent = Nothing
                                                                                  , iTags = []
                                                                                  , iShortDescription = Nothing
                                                                                  , iLongDescription = Nothing
                                                                                  , chapterId = Just 2
                                                                                  , questionId = Just 61
                                                                                  , iLink = Nothing
                                                                                  , iMandatory = False
                                                                                  , iRules = []
                                                                                  , iAutoComplete = []
                                                                                  }
                                                                              , sgLevel = 0
                                                                              , sgItems =
                                                                                  [ ChoiceFI
                                                                                    { chfiDescriptor =
                                                                                        FIDescriptor
                                                                                        { iLabel =
                                                                                            Just
                                                                                              "Who will arrange access control?"
                                                                                        , iNumbering = NoNumbering
                                                                                        , iIdent = Nothing
                                                                                        , iTags = []
                                                                                        , iShortDescription = Nothing
                                                                                        , iLongDescription = Nothing
                                                                                        , chapterId = Just 2
                                                                                        , questionId = Just 61
                                                                                        , iLink = Nothing
                                                                                        , iMandatory = True
                                                                                        , iRules = []
                                                                                        , iAutoComplete = []
                                                                                        }
                                                                                    , chfiAvailableOptions =
                                                                                        [ SimpleOption
                                                                                            "No special provisions are needed"
                                                                                        , SimpleOption
                                                                                            "Project management will need to be able to give people access"
                                                                                        , SimpleOption
                                                                                            "The work space should be connected to a single-sign-on system"
                                                                                        ]
                                                                                    }
                                                                                  ]
                                                                              }
                                                                            , SimpleGroup
                                                                              { sgDescriptor =
                                                                                  FIDescriptor
                                                                                  { iLabel = Nothing
                                                                                  , iNumbering = NoNumbering
                                                                                  , iIdent = Nothing
                                                                                  , iTags = []
                                                                                  , iShortDescription = Nothing
                                                                                  , iLongDescription = Nothing
                                                                                  , chapterId = Just 2
                                                                                  , questionId = Just 62
                                                                                  , iLink = Nothing
                                                                                  , iMandatory = False
                                                                                  , iRules = []
                                                                                  , iAutoComplete = []
                                                                                  }
                                                                              , sgLevel = 0
                                                                              , sgItems =
                                                                                  [ ChoiceFI
                                                                                    { chfiDescriptor =
                                                                                        FIDescriptor
                                                                                        { iLabel =
                                                                                            Just
                                                                                              "Will the work space need to be remote mounted?"
                                                                                        , iNumbering = NoNumbering
                                                                                        , iIdent = Nothing
                                                                                        , iTags = []
                                                                                        , iShortDescription = Nothing
                                                                                        , iLongDescription = Nothing
                                                                                        , chapterId = Just 2
                                                                                        , questionId = Just 62
                                                                                        , iLink = Nothing
                                                                                        , iMandatory = True
                                                                                        , iRules = []
                                                                                        , iAutoComplete = []
                                                                                        }
                                                                                    , chfiAvailableOptions =
                                                                                        [ SimpleOption "No"
                                                                                        , SimpleOption
                                                                                            "Yes, for occasional exploration"
                                                                                        , SimpleOption
                                                                                            "Yes, for actual computations, requiring high performance"
                                                                                        ]
                                                                                    }
                                                                                  ]
                                                                              }
                                                                            , SimpleGroup
                                                                              { sgDescriptor =
                                                                                  FIDescriptor
                                                                                  { iLabel = Nothing
                                                                                  , iNumbering = NoNumbering
                                                                                  , iIdent = Nothing
                                                                                  , iTags = []
                                                                                  , iShortDescription = Nothing
                                                                                  , iLongDescription = Nothing
                                                                                  , chapterId = Just 2
                                                                                  , questionId = Just 63
                                                                                  , iLink = Nothing
                                                                                  , iMandatory = False
                                                                                  , iRules = []
                                                                                  , iAutoComplete = []
                                                                                  }
                                                                              , sgLevel = 0
                                                                              , sgItems =
                                                                                  [ ChoiceFI
                                                                                    { chfiDescriptor =
                                                                                        FIDescriptor
                                                                                        { iLabel =
                                                                                            Just
                                                                                              "Will data be copied out and in to the workspace by remote users?"
                                                                                        , iNumbering = NoNumbering
                                                                                        , iIdent = Nothing
                                                                                        , iTags = []
                                                                                        , iShortDescription = Nothing
                                                                                        , iLongDescription = Nothing
                                                                                        , chapterId = Just 2
                                                                                        , questionId = Just 63
                                                                                        , iLink = Nothing
                                                                                        , iMandatory = True
                                                                                        , iRules = []
                                                                                        , iAutoComplete = []
                                                                                        }
                                                                                    , chfiAvailableOptions =
                                                                                        [ SimpleOption
                                                                                            "No, this should not be allowed"
                                                                                        , SimpleOption
                                                                                            "Yes, occasionally"
                                                                                        , DetailedOption
                                                                                            NoNumbering
                                                                                            "Yes, for actual computations, requiring high performance"
                                                                                            [ SimpleGroup
                                                                                              { sgDescriptor =
                                                                                                  FIDescriptor
                                                                                                  { iLabel = Nothing
                                                                                                  , iNumbering =
                                                                                                      NoNumbering
                                                                                                  , iIdent = Nothing
                                                                                                  , iTags = []
                                                                                                  , iShortDescription =
                                                                                                      Nothing
                                                                                                  , iLongDescription =
                                                                                                      Nothing
                                                                                                  , chapterId = Just 2
                                                                                                  , questionId = Just 63
                                                                                                  , iLink = Nothing
                                                                                                  , iMandatory = True
                                                                                                  , iRules = []
                                                                                                  , iAutoComplete = []
                                                                                                  }
                                                                                              , sgLevel = 0
                                                                                              , sgItems =
                                                                                                  [ SimpleGroup
                                                                                                    { sgDescriptor =
                                                                                                        FIDescriptor
                                                                                                        { iLabel =
                                                                                                            Nothing
                                                                                                        , iNumbering =
                                                                                                            NoNumbering
                                                                                                        , iIdent =
                                                                                                            Nothing
                                                                                                        , iTags = []
                                                                                                        , iShortDescription =
                                                                                                            Nothing
                                                                                                        , iLongDescription =
                                                                                                            Nothing
                                                                                                        , chapterId =
                                                                                                            Just 2
                                                                                                        , questionId =
                                                                                                            Just 64
                                                                                                        , iLink =
                                                                                                            Nothing
                                                                                                        , iMandatory =
                                                                                                            False
                                                                                                        , iRules = []
                                                                                                        , iAutoComplete =
                                                                                                            []
                                                                                                        }
                                                                                                    , sgLevel = 0
                                                                                                    , sgItems =
                                                                                                        [ ChoiceFI
                                                                                                          { chfiDescriptor =
                                                                                                              FIDescriptor
                                                                                                              { iLabel =
                                                                                                                  Just
                                                                                                                    "Are data integrity and reliability requirements also met by the other storage spaces used in the project?"
                                                                                                              , iNumbering =
                                                                                                                  NoNumbering
                                                                                                              , iIdent =
                                                                                                                  Nothing
                                                                                                              , iTags =
                                                                                                                  []
                                                                                                              , iShortDescription =
                                                                                                                  Nothing
                                                                                                              , iLongDescription =
                                                                                                                  Nothing
                                                                                                              , chapterId =
                                                                                                                  Just 2
                                                                                                              , questionId =
                                                                                                                  Just
                                                                                                                    64
                                                                                                              , iLink =
                                                                                                                  Nothing
                                                                                                              , iMandatory =
                                                                                                                  True
                                                                                                              , iRules =
                                                                                                                  []
                                                                                                              , iAutoComplete =
                                                                                                                  []
                                                                                                              }
                                                                                                          , chfiAvailableOptions =
                                                                                                              [ SimpleOption
                                                                                                                  "This is not needed"
                                                                                                              , SimpleOption
                                                                                                                  "Yes"
                                                                                                              ]
                                                                                                          }
                                                                                                        ]
                                                                                                    }
                                                                                                  ]
                                                                                              }
                                                                                            ]
                                                                                        ]
                                                                                    }
                                                                                  ]
                                                                              }
                                                                            ]
                                                                        }
                                                                      ]
                                                                  ]
                                                              }
                                                            ]
                                                        }
                                                      ]
                                                  }
                                                ]
                                            ]
                                        }
                                      ]
                                  }
                                , SimpleGroup
                                  { sgDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 2
                                      , questionId = Just 65
                                      , iLink = Nothing
                                      , iMandatory = False
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , sgLevel = 0
                                  , sgItems =
                                      [ ChoiceFI
                                        { chfiDescriptor =
                                            FIDescriptor
                                            { iLabel = Just "How available/reliable should must the workspace be?"
                                            , iNumbering = NoNumbering
                                            , iIdent = Nothing
                                            , iTags = []
                                            , iShortDescription = Nothing
                                            , iLongDescription = Nothing
                                            , chapterId = Just 2
                                            , questionId = Just 65
                                            , iLink = Nothing
                                            , iMandatory = True
                                            , iRules = []
                                            , iAutoComplete = []
                                            }
                                        , chfiAvailableOptions =
                                            [ SimpleOption "Skip"
                                            , DetailedOption
                                                NoNumbering
                                                "Explore"
                                                [ SimpleGroup
                                                  { sgDescriptor =
                                                      FIDescriptor
                                                      { iLabel = Nothing
                                                      , iNumbering = NoNumbering
                                                      , iIdent = Nothing
                                                      , iTags = []
                                                      , iShortDescription = Nothing
                                                      , iLongDescription = Nothing
                                                      , chapterId = Just 2
                                                      , questionId = Just 65
                                                      , iLink = Nothing
                                                      , iMandatory = True
                                                      , iRules = []
                                                      , iAutoComplete = []
                                                      }
                                                  , sgLevel = 0
                                                  , sgItems =
                                                      [ SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 66
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "What is the acceptable risk for a total loss?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription = Nothing
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 66
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [ SimpleOption "This is unacceptable"
                                                                  , DetailedOption
                                                                      NoNumbering
                                                                      "All essential data is also stored elsewhere"
                                                                      [ SimpleGroup
                                                                        { sgDescriptor =
                                                                            FIDescriptor
                                                                            { iLabel = Nothing
                                                                            , iNumbering = NoNumbering
                                                                            , iIdent = Nothing
                                                                            , iTags = []
                                                                            , iShortDescription = Nothing
                                                                            , iLongDescription = Nothing
                                                                            , chapterId = Just 2
                                                                            , questionId = Just 66
                                                                            , iLink = Nothing
                                                                            , iMandatory = True
                                                                            , iRules = []
                                                                            , iAutoComplete = []
                                                                            }
                                                                        , sgLevel = 0
                                                                        , sgItems =
                                                                            [ SimpleGroup
                                                                              { sgDescriptor =
                                                                                  FIDescriptor
                                                                                  { iLabel = Nothing
                                                                                  , iNumbering = NoNumbering
                                                                                  , iIdent = Nothing
                                                                                  , iTags = []
                                                                                  , iShortDescription = Nothing
                                                                                  , iLongDescription = Nothing
                                                                                  , chapterId = Just 2
                                                                                  , questionId = Just 67
                                                                                  , iLink = Nothing
                                                                                  , iMandatory = False
                                                                                  , iRules = []
                                                                                  , iAutoComplete = []
                                                                                  }
                                                                              , sgLevel = 0
                                                                              , sgItems =
                                                                                  [ ChoiceFI
                                                                                    { chfiDescriptor =
                                                                                        FIDescriptor
                                                                                        { iLabel =
                                                                                            Just
                                                                                              "Is there software in the work space? Can it also be restored quickly?"
                                                                                        , iNumbering = NoNumbering
                                                                                        , iIdent = Nothing
                                                                                        , iTags = []
                                                                                        , iShortDescription = Nothing
                                                                                        , iLongDescription = Nothing
                                                                                        , chapterId = Just 2
                                                                                        , questionId = Just 67
                                                                                        , iLink = Nothing
                                                                                        , iMandatory = True
                                                                                        , iRules = []
                                                                                        , iAutoComplete = []
                                                                                        }
                                                                                    , chfiAvailableOptions =
                                                                                        [ SimpleOption
                                                                                            "There is no software"
                                                                                        , SimpleOption
                                                                                            "Software in the work space is only a copy"
                                                                                        , SimpleOption
                                                                                            "Special care will be taken for the software and configurations"
                                                                                        ]
                                                                                    }
                                                                                  ]
                                                                              }
                                                                            ]
                                                                        }
                                                                      ]
                                                                  ]
                                                              }
                                                            ]
                                                        }
                                                      , SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 68
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "Can you handle it when the work space is off line for a while?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription = Nothing
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 68
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [ SimpleOption
                                                                      "We could handle a few days of offline time per year"
                                                                  , SimpleOption
                                                                      "We can only miss the work space for a few hours during work hours"
                                                                  , SimpleOption
                                                                      "Problems during the evenings and weekends can not wait for work hours to be repaired"
                                                                  ]
                                                              }
                                                            ]
                                                        }
                                                      , SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 69
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "How long can you wait for a restore if the storage fails?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription = Nothing
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 69
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [ SimpleOption
                                                                      "We can wait for repair and a restore from tape"
                                                                  , SimpleOption
                                                                      "A spare copy needs to be deployed quickly"
                                                                  , SimpleOption
                                                                      "No waiting is possible, a hot copy must be ready to take over"
                                                                  ]
                                                              }
                                                            ]
                                                        }
                                                      , SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 70
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "How long can you wait for a restore if you accidentally damage a file?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription = Nothing
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 70
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [ SimpleOption "Days"
                                                                  , SimpleOption "Hours"
                                                                  , SimpleOption
                                                                      "Any user needs to be able to restore an old copy instantaneously"
                                                                  ]
                                                              }
                                                            ]
                                                        }
                                                      , SimpleGroup
                                                        { sgDescriptor =
                                                            FIDescriptor
                                                            { iLabel = Nothing
                                                            , iNumbering = NoNumbering
                                                            , iIdent = Nothing
                                                            , iTags = []
                                                            , iShortDescription = Nothing
                                                            , iLongDescription = Nothing
                                                            , chapterId = Just 2
                                                            , questionId = Just 72
                                                            , iLink = Nothing
                                                            , iMandatory = False
                                                            , iRules = []
                                                            , iAutoComplete = []
                                                            }
                                                        , sgLevel = 0
                                                        , sgItems =
                                                            [ ChoiceFI
                                                              { chfiDescriptor =
                                                                  FIDescriptor
                                                                  { iLabel =
                                                                      Just
                                                                        "Do you need to make backups of project data stored elsewhere into your work space?"
                                                                  , iNumbering = NoNumbering
                                                                  , iIdent = Nothing
                                                                  , iTags = []
                                                                  , iShortDescription = Nothing
                                                                  , iLongDescription =
                                                                      Just
                                                                        "<p class=\"question-description\">Are there any data files e.g. on laptops of project members? Also: supercomputing centers and other high performance computer centers often write in their terms of use that you need to take care of your own backups</p>"
                                                                  , chapterId = Just 2
                                                                  , questionId = Just 72
                                                                  , iLink = Nothing
                                                                  , iMandatory = True
                                                                  , iRules = []
                                                                  , iAutoComplete = []
                                                                  }
                                                              , chfiAvailableOptions =
                                                                  [ SimpleOption "There is no data elsewhere"
                                                                  , SimpleOption
                                                                      "All data elsewhere is adequately backed up"
                                                                  , SimpleOption
                                                                      "We make (automated) backups of all data stored outside of the working area"
                                                                  ]
                                                              }
                                                            ]
                                                        }
                                                      ]
                                                  }
                                                ]
                                            ]
                                        }
                                      ]
                                  }
                                ]
                            }
                          ]
                      ]
                  }
                ]
            }
          ]
      }
    , Chapter
      { chDescriptor =
          FIDescriptor
          { iLabel = Just "Data Capture/Measurement"
          , iNumbering = NoNumbering
          , iIdent = Nothing
          , iTags = []
          , iShortDescription = Nothing
          , iLongDescription = Nothing
          , chapterId = Just 3
          , questionId = Nothing
          , iLink = Nothing
          , iMandatory = False
          , iRules = []
          , iAutoComplete = []
          }
      , chItems =
          [ SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 3
                , questionId = Just 1
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "Who will do the measurements?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription =
                          Just
                            "<p class=\"question-description\">Are there easily accessible specialized service providers for data capture?</p>"
                      , chapterId = Just 3
                      , questionId = Just 1
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions =
                      [ SimpleOption "In the project"
                      , DetailedOption
                          NoNumbering
                          "External party"
                          [ SimpleGroup
                            { sgDescriptor =
                                FIDescriptor
                                { iLabel = Nothing
                                , iNumbering = NoNumbering
                                , iIdent = Nothing
                                , iTags = []
                                , iShortDescription = Nothing
                                , iLongDescription = Nothing
                                , chapterId = Just 3
                                , questionId = Just 1
                                , iLink = Nothing
                                , iMandatory = True
                                , iRules = []
                                , iAutoComplete = []
                                }
                            , sgLevel = 0
                            , sgItems =
                                [ InfoFI
                                  { ifiDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 3
                                      , questionId = Just 1
                                      , iLink = Nothing
                                      , iMandatory = True
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , ifiText = "consider making them partner in the project"
                                  }
                                ]
                            }
                          ]
                      ]
                  }
                ]
            }
          , SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 3
                , questionId = Just 2
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "Is special care needed to get the raw data ready for processing?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription =
                          Just
                            "<p class=\"question-description\">Where does the data come from? And who will need it? Sometimes the raw data is measured somewhere else than where the primary processing is taking place. In such cases the ingestion of the primary data may take special planning.</p>"
                      , chapterId = Just 3
                      , questionId = Just 2
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions = [SimpleOption "No", SimpleOption "Yes"]
                  }
                ]
            }
          , SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 3
                , questionId = Just 3
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "Do you have any non-equipment data capture?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , chapterId = Just 3
                      , questionId = Just 3
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions = [SimpleOption "No", SimpleOption "Yes"]
                  }
                ]
            }
          , SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 3
                , questionId = Just 4
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel =
                          Just
                            "Is there a data integration tool that can handle and combine all the data types you are dealing with in your project?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , chapterId = Just 3
                      , questionId = Just 4
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions = [SimpleOption "No", SimpleOption "Yes"]
                  }
                ]
            }
          ]
      }
    , Chapter
      { chDescriptor =
          FIDescriptor
          { iLabel = Just "Data processing and curation"
          , iNumbering = NoNumbering
          , iIdent = Nothing
          , iTags = []
          , iShortDescription = Nothing
          , iLongDescription = Nothing
          , chapterId = Just 4
          , questionId = Nothing
          , iLink = Nothing
          , iMandatory = False
          , iRules = []
          , iAutoComplete = []
          }
      , chItems =
          [ SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 4
                , questionId = Just 1
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "Workflow development"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription =
                          Just
                            "<p class=\"question-description\">It is likely that you will be developing or modifying the workflow for data processing. There are a lot of aspects of this workflow that can play a role in your data management, such as the use of an existing work flow engine, the use of existing software vs development of new components, and whether every run needs human intervention or whether all data processing can be run in bulk once the work flow has been defined.</p>"
                      , chapterId = Just 4
                      , questionId = Just 1
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions = [SimpleOption "Taken care of", SimpleOption "Drill deeper"]
                  }
                ]
            }
          , SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 4
                , questionId = Just 2
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "How will you make sure to know what exactly has been run?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , chapterId = Just 4
                      , questionId = Just 2
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions = [SimpleOption "Taken care of", SimpleOption "Drill deeper"]
                  }
                ]
            }
          , SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 4
                , questionId = Just 3
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "How will you validate the integrity of the results?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , chapterId = Just 4
                      , questionId = Just 3
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions = [SimpleOption "Taken care of", SimpleOption "Drill deeper"]
                  }
                ]
            }
          , SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 4
                , questionId = Just 4
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "Do you have a contingency plan?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription =
                          Just "<p class=\"question-description\">What will you do if the compute facility is down?</p>"
                      , chapterId = Just 4
                      , questionId = Just 4
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions = [SimpleOption "Wait", SimpleOption "We have an alternative"]
                  }
                ]
            }
          ]
      }
    , Chapter
      { chDescriptor =
          FIDescriptor
          { iLabel = Just "Data integration"
          , iNumbering = NoNumbering
          , iIdent = Nothing
          , iTags = []
          , iShortDescription = Nothing
          , iLongDescription = Nothing
          , chapterId = Just 5
          , questionId = Nothing
          , iLink = Nothing
          , iMandatory = False
          , iRules = []
          , iAutoComplete = []
          }
      , chItems =
          [ SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 5
                , questionId = Just 1
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "What is the framework you will use for data integration?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , chapterId = Just 5
                      , questionId = Just 1
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions = [SimpleOption "Taken care of", SimpleOption "Drill deeper"]
                  }
                ]
            }
          , SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 5
                , questionId = Just 2
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "Will you be using common or exchangeable units?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , chapterId = Just 5
                      , questionId = Just 2
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions = [SimpleOption "No", SimpleOption "Yes"]
                  }
                ]
            }
          , SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 5
                , questionId = Just 3
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "Will you be using common ontologies?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , chapterId = Just 5
                      , questionId = Just 3
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions =
                      [ SimpleOption "No"
                      , DetailedOption
                          NoNumbering
                          "Yes"
                          [ SimpleGroup
                            { sgDescriptor =
                                FIDescriptor
                                { iLabel = Nothing
                                , iNumbering = NoNumbering
                                , iIdent = Nothing
                                , iTags = []
                                , iShortDescription = Nothing
                                , iLongDescription = Nothing
                                , chapterId = Just 5
                                , questionId = Just 3
                                , iLink = Nothing
                                , iMandatory = True
                                , iRules = []
                                , iAutoComplete = []
                                }
                            , sgLevel = 0
                            , sgItems =
                                [ InfoFI
                                  { ifiDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 5
                                      , questionId = Just 3
                                      , iLink = Nothing
                                      , iMandatory = True
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , ifiText = "Choose the ontologies before you start"
                                  }
                                ]
                            }
                          ]
                      ]
                  }
                ]
            }
          , SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 5
                , questionId = Just 4
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "Will there be potential issues with statistical normalization?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , chapterId = Just 5
                      , questionId = Just 4
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions = [SimpleOption "No", SimpleOption "Yes"]
                  }
                ]
            }
          , SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 5
                , questionId = Just 5
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "Do you have all tools to couple the necessary data types?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , chapterId = Just 5
                      , questionId = Just 5
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions = [SimpleOption "No", SimpleOption "Yes"]
                  }
                ]
            }
          ]
      }
    , Chapter
      { chDescriptor =
          FIDescriptor
          { iLabel = Just "Data interpretation"
          , iNumbering = NoNumbering
          , iIdent = Nothing
          , iTags = []
          , iShortDescription = Nothing
          , iLongDescription = Nothing
          , chapterId = Just 6
          , questionId = Nothing
          , iLink = Nothing
          , iMandatory = False
          , iRules = []
          , iAutoComplete = []
          }
      , chItems =
          [ SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 6
                , questionId = Just 1
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel =
                          Just
                            "Will data interpretation and modeling require significant compute infrastructure capacity?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , chapterId = Just 6
                      , questionId = Just 1
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions =
                      [ SimpleOption "Taken care of"
                      , DetailedOption
                          NoNumbering
                          "Yes"
                          [ SimpleGroup
                            { sgDescriptor =
                                FIDescriptor
                                { iLabel = Nothing
                                , iNumbering = NoNumbering
                                , iIdent = Nothing
                                , iTags = []
                                , iShortDescription = Nothing
                                , iLongDescription = Nothing
                                , chapterId = Just 6
                                , questionId = Just 1
                                , iLink = Nothing
                                , iMandatory = True
                                , iRules = []
                                , iAutoComplete = []
                                }
                            , sgLevel = 0
                            , sgItems =
                                [ InfoFI
                                  { ifiDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 6
                                      , questionId = Just 1
                                      , iLink = Nothing
                                      , iMandatory = True
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , ifiText =
                                      "Make sure this has been taken into account in the capacity planning under 'Data design and planning'"
                                  }
                                ]
                            }
                          ]
                      ]
                  }
                ]
            }
          , SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 6
                , questionId = Just 2
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "How will you be making sure there is good provenance of the data analysis?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription =
                          Just
                            "<p class=\"question-description\">Data analysis is normally done manually on a step-by-step basis. It is essential to make sure all steps are properly documented, otherwise results will not be reproducible.</p>"
                      , chapterId = Just 6
                      , questionId = Just 2
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions = [SimpleOption "Taken care of", SimpleOption "Drill deeper"]
                  }
                ]
            }
          , SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 6
                , questionId = Just 3
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "Will you be doing (automated) knowledge discovery?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , chapterId = Just 6
                      , questionId = Just 3
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions = [SimpleOption "No", SimpleOption "Yes"]
                  }
                ]
            }
          ]
      }
    , Chapter
      { chDescriptor =
          FIDescriptor
          { iLabel = Just "Information and insight"
          , iNumbering = NoNumbering
          , iIdent = Nothing
          , iTags = []
          , iShortDescription = Nothing
          , iLongDescription = Nothing
          , chapterId = Just 7
          , questionId = Nothing
          , iLink = Nothing
          , iMandatory = False
          , iRules = []
          , iAutoComplete = []
          }
      , chItems =
          [ SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 7
                , questionId = Just 1
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "Will you be working with the philosophy 'as open as possible' for your data?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , chapterId = Just 7
                      , questionId = Just 1
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions =
                      [ DetailedOption
                          NoNumbering
                          "No"
                          [ SimpleGroup
                            { sgDescriptor =
                                FIDescriptor
                                { iLabel = Nothing
                                , iNumbering = NoNumbering
                                , iIdent = Nothing
                                , iTags = []
                                , iShortDescription = Nothing
                                , iLongDescription = Nothing
                                , chapterId = Just 7
                                , questionId = Just 1
                                , iLink = Nothing
                                , iMandatory = True
                                , iRules = []
                                , iAutoComplete = []
                                }
                            , sgLevel = 0
                            , sgItems =
                                [ InfoFI
                                  { ifiDescriptor =
                                      FIDescriptor
                                      { iLabel = Nothing
                                      , iNumbering = NoNumbering
                                      , iIdent = Nothing
                                      , iTags = []
                                      , iShortDescription = Nothing
                                      , iLongDescription = Nothing
                                      , chapterId = Just 7
                                      , questionId = Just 1
                                      , iLink = Nothing
                                      , iMandatory = True
                                      , iRules = []
                                      , iAutoComplete = []
                                      }
                                  , ifiText = "You will need to explain!"
                                  }
                                ]
                            }
                          ]
                      , SimpleOption "Yes"
                      ]
                  }
                ]
            }
          , SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 7
                , questionId = Just 2
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just " Are there legal reasons why (some of your) data can not be completely open?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , chapterId = Just 7
                      , questionId = Just 2
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions = [SimpleOption "No", SimpleOption "Yes"]
                  }
                ]
            }
          , SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 7
                , questionId = Just 3
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just " Are there business reasons why (some of your) data can not be completely open?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , chapterId = Just 7
                      , questionId = Just 3
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions = [SimpleOption "No", SimpleOption "Yes"]
                  }
                ]
            }
          , SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 7
                , questionId = Just 4
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "Where will you make your data available?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , chapterId = Just 7
                      , questionId = Just 4
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions = [SimpleOption "Skip", SimpleOption "Drill Deeper"]
                  }
                ]
            }
          , SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 7
                , questionId = Just 5
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "Did you work out the financial aspects of making the data available?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , chapterId = Just 7
                      , questionId = Just 5
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions = [SimpleOption "Skip", SimpleOption "Drill Deeper"]
                  }
                ]
            }
          , SimpleGroup
            { sgDescriptor =
                FIDescriptor
                { iLabel = Nothing
                , iNumbering = NoNumbering
                , iIdent = Nothing
                , iTags = []
                , iShortDescription = Nothing
                , iLongDescription = Nothing
                , chapterId = Just 7
                , questionId = Just 6
                , iLink = Nothing
                , iMandatory = False
                , iRules = []
                , iAutoComplete = []
                }
            , sgLevel = 0
            , sgItems =
                [ ChoiceFI
                  { chfiDescriptor =
                      FIDescriptor
                      { iLabel = Just "Will you be archiving data?"
                      , iNumbering = NoNumbering
                      , iIdent = Nothing
                      , iTags = []
                      , iShortDescription = Nothing
                      , iLongDescription = Nothing
                      , chapterId = Just 7
                      , questionId = Just 6
                      , iLink = Nothing
                      , iMandatory = True
                      , iRules = []
                      , iAutoComplete = []
                      }
                  , chfiAvailableOptions = [SimpleOption "No", SimpleOption "Yes"]
                  }
                ]
            }
          ]
      }
    ]
