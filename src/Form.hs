{-# LANGUAGE OverloadedStrings #-}

module Form where

import Prelude
import Data.Monoid ((<>))
import Data.Maybe (catMaybes)
import Control.Monad (join)
import Haste (JSString)
import Haste.Ajax

import Model.Question 
import FormEngine.JQuery as JQ
import FormEngine.FormItem as FI
import FormEngine.FormElement.FormElement as E
import FormEngine.FormElement.Identifiers
import FormEngine.FormElement.Rendering
import FormEngine.FormElement.Tabs
import FormEngine.FormContext
import FormEngine.Functionality
import Overlay (overlayOn)
import Texts (bookLabelTxt, bookAckTxt)

import Config.Config (staticURL)

generateForm :: [FormElement] -> IO ()
generateForm tabs = do
  formJq <- select "#form"
  let allTabs = aboutTab : tabs
  _ <- renderTabGroup allTabs (aboutTabPaneJq : tabsContentsJq tabs) formJq
  _ <- selectTab 0 allTabs
  fireClicks
  where
    tabsContentsJq :: [FormElement] -> [IO JQuery]
    tabsContentsJq = map makePaneJq
      where
        makePaneJq :: FormElement -> IO JQuery
        makePaneJq tab = select "<div class='main-pane'>" >>= makeFormSubPane >>= makeDescSubPane
          where
            makeFormSubPane :: JQuery -> IO JQuery
            makeFormSubPane jq =
              appendT "<div class='form-subpane'>" jq >>= inside >>=
              foldElements
                (E.children tab)
                formContext
                ElemBehaviour
                { focusAction = Nothing
                , blurAction = Nothing
                , detailsFunc =
                  Just
                    Functionality
                    { funcImg = "<img alt='details' src='" <> staticURL <> "img/question.png'/>"
                    , funcAction = showDetails
                    }
                } >>=
              JQ.parent
              where
                formContext =
                  FormContext
                  { allElems = tabs
                  , validImg = "<img alt='valid' class='validity-flag' src='" <> staticURL <> "img/valid.png'/>"
                  , invalidImg = "<img alt='invalid' class='validity-flag' src='" <> staticURL <> "img/invalid.png'/>"
                  }
                showDetails :: ElemAction
                showDetails element _ = do
                  let maybeChid = FI.chapterId $ fiDescriptor $ formItem element
                  let maybeQid = FI.questionId $ fiDescriptor $ formItem element
                  case maybeChid of
                    Nothing -> return ()
                    Just chid ->
                      case maybeQid of
                        Nothing -> return ()
                        Just qid ->
                          ajaxRequest
                            POST
                            "api/getQuestion"
                            [("chid" :: JSString, show chid), ("qid" :: JSString, show qid)]
                            getBookContents
                          where getBookContents :: Maybe String -> IO ()
                                getBookContents maybeQuestionStr = 
                                  ajaxRequest
                                    POST
                                    "api/getBookContents"
                                    [("chid" :: JSString, show chid), ("qid" :: JSString, show qid)]
                                    (displayDetails $ read <$> maybeQuestionStr)
                      where displayDetails :: Maybe Question -> Maybe String -> IO ()
                            displayDetails maybeQuestion maybeBookContents = do
                              _ <- overlayOn detailsHtml
                              return ()
                              where
                                detailsHtml =
                                  concat $
                                  [bookLabel] <> catMaybes [maybeBookContents, join $ otherInfo <$> maybeQuestion] <> [bookAck]
                                  where
                                    bookLabel :: String
                                    bookLabel =
                                      case join $ bookRef <$> maybeQuestion of
                                        Nothing -> ""
                                        Just ref -> bookLabelTxt ref
                                    bookAck :: String
                                    bookAck = 
                                      case join $ bookRef <$> maybeQuestion of
                                        Nothing -> ""
                                        Just _ -> bookAckTxt

            makeDescSubPane :: JQuery -> IO JQuery
            makeDescSubPane jq  =
              appendT "<div class='desc-subpane'>" jq >>= setAttrInside "id" (descSubpaneId tab) >>= inside >>=
              appendT "<p class='long-desc'>" >>=
              setAttrInside "id" (descSubpaneParagraphId tab) >>=
              inside >>=
              appendT ("<img src='" <> staticURL <> "img/hint-icon.png' style='margin-right: 5px;'>") >>=
              appendT "<span/>" >>=
              JQ.parent >>=
              JQ.parent
    fireClicks :: IO ()
    fireClicks = do
      _ <- select "input:checked" >>= click >>= click
      _ <- select "input" >>= mouseleave
      _ <- select "textarea" >>= mouseleave
      _ <- select "select" >>= mouseleave
      return ()

aboutTab :: FormElement
aboutTab =
  ChapterElem
  { chfi =
    Chapter
    { chDescriptor =
      FIDescriptor
      { iLabel = Just "About"
      , iNumbering = Numbering [1000] 0
      , iIdent = Nothing
      , iTags = []
      , iShortDescription = Nothing
      , iLongDescription = Nothing
      , FI.chapterId = Nothing
      , FI.questionId = Nothing
      , iLink = Nothing
      , iRules = []
      , iMandatory = False
      }
    , chItems = []
    }
  , chElements = []
  , visited = False
  }

aboutTabPaneJq :: IO JQuery
aboutTabPaneJq =
  select
    "\
\  <div>\
\    <p>\
\      Questionnaire generated from precompiler JSON of <a href=\"https://github.com/CCMi-FIT/ds-km\" target=\"_blank\">Data Stewardship Knowledge Model</a>.\
\    </p>\
\  </div>\
\ "
