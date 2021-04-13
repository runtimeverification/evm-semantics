#!/usr/bin/env node
const { buildSitemap } = require("k-web-theme");
const path = require("path");

const websiteOrigin = process.argv[2];
buildSitemap({
  websiteOrigin,
  websiteDirectory: path.join(__dirname, "../public_content/"),
  sitemapPath: path.join(__dirname, "../public_content/sitemap.xml"),
  ignore: (url) => url.endsWith(".html"),
});
