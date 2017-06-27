{-# LANGUAGE OverloadedStrings #-}

module KMTransform
  ( transformQuestionnaire
  , distillQuestionnaire
  ) where

import Data.List (find)
import Data.Maybe
import Data.Monoid ((<>))
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as T
import qualified Database.PostgreSQL.Simple as PG

import FormEngine.FormItem
import KModel as Model

-- Helper routines
transformText :: Maybe Text -> Text
transformText = fromMaybe ""

makeHtmlLink :: Text -> Text -> Bool -> Text
makeHtmlLink link anchor newtab = "<a href=\"" <> link <> "\" target=\"" <> target <> "\">" <> anchor <> "</a>"
  where
    target =
      if newtab
        then "_blank"
        else "_self"

transformExpert :: Model.Expert -> Text
transformExpert e =
  case expertEmail e of
    Nothing -> expertName e
    Just address -> makeHtmlLink ("mailto:" <> address) (expertName e) True

transformReference :: Model.Reference -> Text
transformReference r =
  case refType r of
    "dmpbook" -> "" -- handled by Ajax loading from database
    "xref" -> "Reference to other question (not implemented yet)"
    "url" ->
      case urlrefText r of
        Nothing -> makeHtmlLink url url True
        Just anchor -> makeHtmlLink url anchor True
      where url = transformText . urlrefLink $ r
    _ -> "Unrecognized reference"

buildLongDesc :: Model.Question -> Maybe Text
buildLongDesc q =
  if T.null longDesc
    then Nothing
    else Just longDesc
  where
    longDesc = Prelude.foldl (<>) "" (catMaybes longDescParts)
    longDescParts = [fmap wrapText (questText q)]
    wrapText txt = "<p class=\"question-description\">" <> txt <> "</p>"

getBookRef :: Model.Question -> Maybe Text
getBookRef q =
  let maybeRef = find (\r -> refType r == "dmpbook") <$> questRefs q
  in case maybeRef of
       Just (Just ref) -> dmpChapter ref
       _ -> Nothing

-- Transformation routines
transformQuestionnaire :: [Model.Chapter] -> [FormItem]
transformQuestionnaire = map transformChapter

transformChapter :: Model.Chapter -> FormItem
transformChapter ch =
  FormEngine.FormItem.Chapter
  { chDescriptor = defaultFIDescriptor {iLabel = Just (chapTitle ch), chapterId = Just $ chapID ch}
  , chItems = intro ++ map (transformQuestion ch) (chapQuests ch)
  }
  where
    intro =
      case chapText ch of
        Just introText ->
          [InfoFI {ifiDescriptor = defaultFIDescriptor {chapterId = Just $ chapID ch}, ifiText = introText}]
        _ -> []

transformQuestion :: Model.Chapter -> Model.Question -> FormItem
transformQuestion ch q =
  SimpleGroup
  { sgDescriptor = defaultFIDescriptor {chapterId = Just $ chapID ch, questionId = Just $ questID q}
  , sgLevel = 0
  , sgItems = question : follows
  }
  where
    question =
      case questType q of
        "option" -> transformOptionQuestion ch q
        "list" -> transformListQuestion ch q
        _ -> transformFieldQuestion ch q
    follows =
      case questType q of
        "list" -> []
        _ -> map (transformQuestion ch) (fromMaybe [] . questFollow $ q)

transformOptionQuestion :: Model.Chapter -> Model.Question -> FormItem
transformOptionQuestion ch q =
  ChoiceFI
  { chfiDescriptor =
      defaultFIDescriptor
      { iLabel = Just (questTitle q)
      , iLongDescription = buildLongDesc q
      , chapterId = Just $ chapID ch
      , questionId = Just $ questID q
      , iMandatory = True
      }
  , chfiAvailableOptions = map transformAnswer (fromMaybe [] . questAnswers $ q)
  }
  where
    transformAnswer :: Model.Answer -> Option
    transformAnswer a =
      if hasFollows
        then DetailedOption NoNumbering (answerLabel a) [followsGroup]
        else SimpleOption (answerLabel a)
      where
        hasFollows :: Bool
        hasFollows = (isJust . answerFollow $ a) || (isJust . answerAdvice $ a)
        followsGroup :: FormItem
        followsGroup =
          SimpleGroup
          { sgDescriptor =
              defaultFIDescriptor {chapterId = Just $ chapID ch, questionId = Just $ questID q, iMandatory = True}
          , sgLevel = 0
          , sgItems = followAdvice ++ followsQuestions
          }
        followsQuestions :: [FormItem]
        followsQuestions = map (transformQuestion ch) (fromMaybe [] . answerFollow $ a)
        followAdvice :: [FormItem]
        followAdvice =
          case answerAdvice a of
            Just advice ->
              [ InfoFI
                { ifiDescriptor =
                    defaultFIDescriptor {chapterId = Just $ chapID ch, questionId = Just $ questID q, iMandatory = True}
                , ifiText = advice
                }
              ]
            _ -> []

transformListQuestion :: Model.Chapter -> Model.Question -> FormItem
transformListQuestion ch q =
  MultipleGroup
  { mgDescriptor =
      defaultFIDescriptor
      { iLabel = Just (questTitle q)
      , iShortDescription = Just "List all the items bellow."
      , iLongDescription = buildLongDesc q
      , chapterId = Just $ chapID ch
      , questionId = Just $ questID q
      , iMandatory = True
      }
  , mgLevel = 0
  , mgItems =
      StringFI
      { sfiDescriptor =
          defaultFIDescriptor
          { iLabel = Just "Item"
          , iLongDescription = buildLongDesc q
          , chapterId = Just $ chapID ch
          , questionId = Just $ questID q
          }
      } :
      follows
  }
  where
    follows = map (transformQuestion ch) (fromMaybe [] . questFollow $ q)

transformFieldQuestion :: Model.Chapter -> Model.Question -> FormItem
transformFieldQuestion ch q =
  case questType q of
    "text" -> TextFI {tfiDescriptor = qFI}
    "number" -> NumberFI {nfiDescriptor = qFI, nfiUnit = NoUnit}
    "email" -> EmailFI {efiDescriptor = qFI}
    _ -> StringFI {sfiDescriptor = qFI}
  where
    qFI =
      defaultFIDescriptor
      { iLabel = Just (questTitle q)
      , iLongDescription = questText q
      , chapterId = Just $ chapID ch
      , questionId = Just $ questID q
      , iMandatory = True
      }

-- Generating details
distillQuestionnaire :: PG.Connection -> [Model.Chapter] -> IO ()
distillQuestionnaire pgConn = mapM_ (distillChapter pgConn)

distillChapter :: PG.Connection -> Model.Chapter -> IO ()
distillChapter pgConn ch = mapM_ (distillQuestion pgConn ch) (chapQuests ch)

distillQuestion :: PG.Connection -> Model.Chapter -> Model.Question -> IO ()
distillQuestion pgConn ch q = do
  case questType q of
    "option" -> distillOptionQuestion pgConn ch q
    "list" -> do
      _ <- storeDetails pgConn ch q
      return ()
    _ -> return ()
  mapM_ (distillQuestion pgConn ch) (fromMaybe [] . questFollow $ q)

distillOptionQuestion :: PG.Connection -> Model.Chapter -> Model.Question -> IO ()
distillOptionQuestion pgConn ch q = do
  _ <- storeDetails pgConn ch q
  mapM_ distillAnswer (fromMaybe [] . questAnswers $ q)
  where
    distillAnswer :: Model.Answer -> IO ()
    distillAnswer a =
      case answerFollow a of
        Just follows -> mapM_ (distillQuestion pgConn ch) follows
        _ -> return ()

storeDetails :: PG.Connection -> Model.Chapter -> Model.Question -> IO ()
storeDetails pgConn ch q = do
  _ <-
    PG.execute
      pgConn
      "INSERT INTO \"Questions\" (chapterId, questionId, bookRef, otherInfo) VALUES (?, ?, ?, ?)"
      (chapID ch, questID q, getBookRef q, otherInfo)
  return ()
  where
    otherInfo :: Maybe Text
    otherInfo =
      if T.null info
        then Nothing
        else Just info
      where
        info = Prelude.foldl (<>) "" (catMaybes infoParts)
        infoParts = [fmap wrapExps (questExps q), fmap wrapRefs (questRefs q)]
        wrapExps exps = "<p class=\"question-experts\">Experts:<ul>" <> T.concat (expertItems exps) <> "</ul></p>"
        wrapRefs refs = "<p class=\"question-references\">References:<ul>" <> T.concat (referItems refs) <> "</ul></p>"
        expertItems = fmap (enlist . transformExpert)
        referItems = fmap (enlist . transformReference)
        enlist item = "<li>" <> item <> "</li>"
