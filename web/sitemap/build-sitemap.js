#!/usr/bin/env node
const getPort = require("get-port");
const express = require("express");
const path = require("path");
const SitemapGenerator = require("sitemap-generator");
const fs = require("fs");

(async () => {
  const app = express();
  const port = await getPort();
  app.use(express.static(path.resolve(__dirname, "../public_content/")));
  const server = app.listen(port);
  const websiteUrl = `http://127.0.0.1:${port}/`;
  console.log(":: running server at: ", websiteUrl);

  const filePath = path.resolve(__dirname, "../public_content/sitemap.xml");
  const websiteOrigin = process.argv[2];

  const generator = SitemapGenerator(websiteUrl, {
    stripQuerystring: true,
    filepath: filePath,
    lastMod: true,
    changeFreq: "monthly",
  });

  generator.on("add", (url) => {
    console.log("* add url: ", url);
  });

  generator.on("done", () => {
    fs.readFile(filePath, (error, data) => {
      const arr = data.toString("utf-8").split("\n");
      let newContent = "";
      arr.forEach((line) => {
        if (line.match(/<loc>/)) {
          const url = line.match(/<loc>(.+?)<\/loc>/)[1];
          line = line.replace(websiteUrl, websiteOrigin);
          if (url.match(/\.(pdf|pptx?)$/)) {
            // pdf like files
            newContent += line + "\n";
            newContent += "    <priority>0.5</priority>\n";
          } else {
            // web pages
            newContent += line + "\n";
            newContent += "    <priority>1.0</priority>\n";
          }
        } else {
          newContent += line + "\n";
        }
      });
      newContent = newContent.trim();
      fs.writeFileSync(filePath, newContent);
    });

    console.log("* sitemaps created");
    server.close();
  });

  // start the crawler
  console.log("* spawn crawler");
  generator.start();
})();
