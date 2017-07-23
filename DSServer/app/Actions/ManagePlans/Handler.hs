{-# LANGUAGE OverloadedStrings #-}

module Actions.ManagePlans.Handler (handler) where

import qualified Data.Text as T
import Data.Monoid ((<>))
import Data.Maybe (fromMaybe)
import Text.Blaze.Html5 (Html, (!), textValue)
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A

import Config.Config (staticURL)
import App (Action, PGPool, Cookies, runQuery)
import Auth (checkLogged)
import Model.User
import Model.Plan
import qualified Persistence.Plan as P
import qualified Page
import qualified Actions.ManagePlans.Add.Url as Actions.ManagePlans.Add
import qualified Actions.ManagePlans.Delete.Url as Actions.ManagePlans.Delete
import qualified Actions.ManagePlans.Open.Url as Actions.ManagePlans.Open
import qualified Bridge as B

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

view :: User -> [Plan] -> Html
view user plans = do
  H.h2 "Your plans:"
  H.table ! A.class_ "plans" $ do
    H.thead $
      H.tr $ do
        H.th ! A.class_ "name" $ "Name"
        H.th ! A.class_ "description" $ "Description"
        H.th mempty
    H.tbody $ do
      renderTableRows
      H.tr $ do
        H.th ! A.colspan "3" ! A.style "text-align: left" $
          H.a ! A.href (textValue $ T.pack Actions.ManagePlans.Add.url) $
            H.img ! A.class_ "table-action" ! A.src (textValue $ T.pack staticURL <> "img/plus.png") ! A.alt "Add"
  where
    renderTableRows :: Html
    renderTableRows = mapM_ renderTableRow plans
      where
      renderTableRow plan = let openCss = if isPlanOpened user plan then A.class_ "open" else A.class_ "" in
        H.tr ! openCss $ do
          H.td
            ! A.class_ "editable"
            ! A.onclick (textValue $ T.pack $ B.call1 B.PlanNameEdit (show $ p_id plan))
            $ H.toHtml $ p_name plan
          H.td ! A.class_ "editable"
            ! A.onclick (textValue $ T.pack $ B.call1 B.PlanDescriptionEdit (show $ p_id plan))
            $ H.toHtml $ fromMaybe "" $ p_description plan
          H.td renderActions
        where
        renderActions = do
          H.a ! A.href (textValue $ T.pack $ Actions.ManagePlans.Delete.url ++ "?planId=" ++ show (p_id plan)) $
            H.img ! A.class_ "table-action" ! A.src (textValue $ T.pack staticURL <> "img/minus.png") ! A.alt "Delete"
          if not $ isPlanOpened user plan then
            H.a ! A.href (textValue $ T.pack $ Actions.ManagePlans.Open.url ++ "?planId=" ++ show (p_id plan)) $
              H.img ! A.class_ "table-action" ! A.src (textValue $ T.pack staticURL <> "img/open.png") ! A.alt "Open"
          else mempty

isPlanOpened :: User -> Plan -> Bool
isPlanOpened user plan = case u_open_plan_id user of
    Nothing -> False
    Just upid -> p_id plan == upid

handler :: PGPool -> Cookies -> Action
handler pool cookies = checkLogged pool cookies (\user -> do
  plans <- runQuery pool $ P.getPlansOfUser user
  Page.render (view user plans) Page.defaultPageConfig { Page.pc_mUser = Just user }
  )
