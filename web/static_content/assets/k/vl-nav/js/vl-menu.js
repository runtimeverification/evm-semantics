/*
 * Created by VectorLab.
 * version 1.0
 * Copyright (c) 2018 "VectorLab"
 * http://thevectorlab.net
 */

/*
 * jQuery throttle / debounce - v1.1 - 3/7/2010
 * http://benalman.com/projects/jquery-throttle-debounce-plugin/
 *
 * Copyright (c) 2010 "Cowboy" Ben Alman
 * Dual licensed under the MIT and GPL licenses.
 * http://benalman.com/about/license/
 */

(function (b, c) {
    var $ = b.jQuery || b.Cowboy || (b.Cowboy = {}), a;
    $.throttle = a = function (e, f, j, i) {
        var h, d = 0;
        if (typeof f !== "boolean") {
            i = j;
            j = f;
            f = c
        }
        function g() {
            var o = this, m = +new Date() - d, n = arguments;

            function l() {
                d = +new Date();
                j.apply(o, n)
            }

            function k() {
                h = c
            }

            if (i && !h) {
                l()
            }
            h && clearTimeout(h);
            if (i === c && m > e) {
                l()
            } else {
                if (f !== true) {
                    h = setTimeout(i ? k : l, i === c ? e - m : e)
                }
            }
        }

        if ($.guid) {
            g.guid = j.guid = j.guid || $.guid++
        }
        return g
    };
    $.debounce = function (d, e, f) {
        return f === c ? a(d, e, false) : a(d, f, e !== false)
    }
})(window);


/*
 * vlmenu - dropdown mega menu
 * Created by VectorLab.
 * version 1.0
 * Copyright (c) 2018 "VectorLab"
 * http://thevectorlab.net
 */


window.vlmenu = {
    defaults:{
        selector:".vlmenu",
        breakpoint:1024
    },
    settings:{},
    prepare: function () {

        $('.nav-btn').click(function () {
            $('ul'+vlmenu.settings.selector).toggle();
        });

        $(vlmenu.settings.selector + "li.menu-right").addClass('vl-r-align');
    },
    fixMenu: function () {
        var w = $(window).width();

        if ($(window).width() > vlmenu.settings.breakpoint) {
            $('ul'+vlmenu.settings.selector).removeAttr('style');
        }

        if (w <= vlmenu.settings.breakpoint) {
            $(vlmenu.settings.selector).removeClass('fade-effect slide-effect');
            $(".vl-r-align").removeClass('menu-right');
            $(vlmenu.settings.selector+" li").has('ul').find('a:eq(0)').addClass("vl-accordion");
            $(vlmenu.settings.selector+" li").has('.mega-menu').find('a:eq(0)').addClass("vl-accordion");
            $(vlmenu.settings.selector + ' ul, .vlmenu li > div').addClass('hidden-sub');
        } else {
            $(vlmenu.settings.selector+" li").has('ul').find('a:eq(0)').removeClass("vl-accordion");
            $(vlmenu.settings.selector+" li").has('.mega-menu').find('a:eq(0)').removeClass("vl-accordion");
            $(".vl-r-align").addClass('menu-right');
            $(vlmenu.settings.selector).addClass('fade-effect slide-effect');
            $(vlmenu.settings.selector + ' ul, .vlmenu li > div').removeClass('hidden-sub');
        }
    },
    addIconToParent: function () {
//             $("li").has('ul').find('a:eq(0)').append(icon);
        $(vlmenu.settings.selector + " li").has('ul').find('a:eq(0)').each(function () {
            $(this).html($(this).html() + "<i class='arrow fa fa-angle-right'/>");
        });
        $(vlmenu.settings.selector + " li").has('.mega-menu').find('a:eq(0)').each(function () {
            $(this).html($(this).html() + "<i class='arrow fa fa-angle-right'/>");
        });

    },
    makeAccordionInResponsiveView: function () {

        $(vlmenu.settings.selector).on("click", 'a.vl-accordion', function (e) {

            var children = $(this).next('ul').find(".visible-sub");
            var parents = $(this).parents(".visible-sub");


            if($(this).hasClass("vl-accordion-open")){
                $(this).next('ul').removeClass("visible-sub").addClass('hidden-sub');
                $(this).next('ul').find('ul').removeClass("visible-sub").addClass('hidden-sub');

                $(this).next('.mega-menu').removeClass("visible-sub").addClass('hidden-sub');

                $(this).removeClass("vl-accordion-open");
                return true;
            } else {
                $(".vl-accordion-open").removeClass("vl-accordion-open");
                $(this).parents('li').find('a:eq(0)').addClass("vl-accordion-open");
                $(this).addClass("vl-accordion-open");
            }

            $(".visible-sub").not(parents).not(children).toggleClass('hidden-sub visible-sub');
            $(this).next('ul').toggleClass('hidden-sub visible-sub');
            $(this).next('.mega-menu').toggleClass('hidden-sub visible-sub');
        });
    },
    init:function(options){
        vlmenu.settings = $.extend(vlmenu.defaults,options);
        vlmenu.prepare();
        vlmenu.fixMenu();
        // vlmenu.addIconToParent();
        vlmenu.makeAccordionInResponsiveView();

        $(window).resize($.debounce(250, vlmenu.fixMenu));
    }
}
