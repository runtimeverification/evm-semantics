/* ---------------------------------------------
 common scripts
 --------------------------------------------- */

(function () {
  "use strict"; // use strict to start

  /* ---------------------------------------------
     WOW init
     --------------------------------------------- */

  new WOW().init();

  $(document).ready(function () {
    // Sidebar menu
    $(".bd-search-docs-toggle").click(() => {
      if ($(".bd-search-docs-toggle").hasClass("collapsed")) {
        $(".bd-sidebar > nav").addClass("show");
        $(".bd-search-docs-toggle").removeClass("collapsed");
      } else {
        $(".bd-sidebar > nav").removeClass("show");
        $(".bd-search-docs-toggle").addClass("collapsed");
      }
    });

    // Search box
    $("#search-box").keydown((event) => {
      if (event.which === 13) {
        event.stopPropagation();
        event.preventDefault();
        window.open(
          `https://www.google.com/search?q=site:${
            location.hostname.match(/\.github\.io/)
              ? location.hostname + "/evm-semantics"
              : location.hostname
          }%20${encodeURIComponent($("#search-box").val())}`,
          "_blank"
        );
      }
    });
  });
})(jQuery);
