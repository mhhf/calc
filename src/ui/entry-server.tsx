// @refresh reload
import { createHandler, StartServer } from "@solidjs/start/server";

export default createHandler(() => (
  <StartServer
    document={({ assets, children, scripts }) => (
      <html lang="en">
        <head>
          <meta charset="utf-8" />
          <meta name="viewport" content="width=device-width, initial-scale=1" />
          <link rel="icon" href="/favicon.ico" />
          <title>CALC - Linear Logic Proof Assistant</title>
          {assets}
        </head>
        <body class="bg-gray-950 text-gray-100 min-h-screen">
          <div id="app">{children}</div>
          {scripts}
        </body>
      </html>
    )}
  />
));
