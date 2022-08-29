const { cleanUpFiles, generatePagesFromMarkdownFiles } = require("k-web-theme");
const path = require("path");
const fs = require("fs");

const pageTemplate = fs
  .readFileSync("./static_content/html/page_template.html")
  .toString("utf-8");
generatePagesFromMarkdownFiles({
  globPattern: path.resolve(__dirname, "../") + "/**/*.md",
  globOptions: {
    ignore: [
      path.resolve(__dirname, "../web/**/*"),
      path.resolve(__dirname, "../deps/k/**/*"),
    ],
  },
  origin: "https://github.com/kframework/evm-semantics/tree/master/",
  sourceDirectory: path.resolve(__dirname, "../"),
  outputDirectory: path.resolve(__dirname, "./public_content/"),
  websiteOrigin: "https://jellopaper.org",
  websiteDirectory: path.resolve(__dirname, "./public_content/"),
  includeFileBasePath: path.resolve(__dirname, "./static_content/html/"),
  template: pageTemplate,
});
