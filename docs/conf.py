#!/usr/bin/env python3
# -*- coding: utf-8 -*-
#
# mockturtle documentation build configuration file, created by
# sphinx-quickstart on Thu Nov 30 18:28:14 2017.
#
# This file is execfile()d with the current directory set to its
# containing dir.
#
# Note that not all possible configuration values are present in this
# autogenerated file.
#
# All configuration values have a default; values that are commented out
# serve to show the default.

# If extensions (or modules to document with autodoc) are in another directory,
# add these directories to sys.path here. If the directory is relative to the
# documentation root, use os.path.abspath to make it absolute, like shown here.
#
# import os
# import sys
# sys.path.insert(0, os.path.abspath('.'))


# -- General configuration ------------------------------------------------

# If your documentation needs a minimal Sphinx version, state it here.
#
# needs_sphinx = '1.0'

# Add any Sphinx extension module names here, as strings. They can be
# extensions coming with Sphinx (named 'sphinx.ext.*') or your custom
# ones.
extensions = ['sphinx.ext.mathjax', 'sphinx.ext.viewcode', 'breathe']

# Add any paths that contain templates here, relative to this directory.
templates_path = ['_templates']

# The suffix(es) of source filenames.
# You can specify multiple suffix as a list of string:
#
# source_suffix = ['.rst', '.md']
source_suffix = '.rst'

# The master toctree document.
master_doc = 'index'

# General information about the project.
project = 'mockturtle'
copyright = '2018-2021, EPFL LSI'
author = 'EPFL LSI'

# The version info for the project you're documenting, acts as replacement for
# |version| and |release|, also used in various other places throughout the
# built documents.
#
# The short X.Y version.
version = 'v0.3'
# The full version, including alpha/beta/rc tags.
release = 'v0.3'

# The language for content autogenerated by Sphinx. Refer to documentation
# for a list of supported languages.
#
# This is also used if you do content translation via gettext catalogs.
# Usually you set "language" from the command line for these cases.
language = None

# List of patterns, relative to source directory, that match files and
# directories to ignore when looking for source files.
# This patterns also effect to html_static_path and html_extra_path
exclude_patterns = ['_build', 'Thumbs.db', '.DS_Store']

# The name of the Pygments (syntax highlighting) style to use.
pygments_style = 'sphinx'

# If true, `todo` and `todoList` produce output, else they produce nothing.
todo_include_todos = False


# -- Options for HTML output ----------------------------------------------

# The theme to use for HTML and HTML Help pages.  See the documentation for
# a list of builtin themes.
#
html_theme = 'sphinx_rtd_theme'

# Theme options are theme-specific and customize the look and feel of a theme
# further.  For a list of options available for each theme, see the
# documentation.
#
html_theme_options = {
    "collapse_navigation" : False
}

# Add any paths that contain custom static files (such as style sheets) here,
# relative to this directory. They are copied after the builtin static files,
# so a file named "default.css" will overwrite the builtin "default.css".
html_static_path = ['_static']

# Custom sidebar templates, must be a dictionary that maps document names
# to template names.
#
# This is required for the alabaster theme
# refs: http://alabaster.readthedocs.io/en/latest/installation.html#sidebars
html_sidebars = {
    '**': [
        'about.html',
        'navigation.html',
        'relations.html',  # needs 'show_related': True theme option to display
        'searchbox.html',
        'donate.html',
    ]
}


# -- Options for HTMLHelp output ------------------------------------------

# Output file base name for HTML help builder.
htmlhelp_basename = 'mockturtledoc'


# -- Options for LaTeX output ---------------------------------------------

latex_elements = {
    # The paper size ('letterpaper' or 'a4paper').
    #
    # 'papersize': 'letterpaper',

    # The font size ('10pt', '11pt' or '12pt').
    #
    # 'pointsize': '10pt',

    # Additional stuff for the LaTeX preamble.
    #
    # 'preamble': '',

    # Latex figure (float) alignment
    #
    # 'figure_align': 'htbp',
}

# Grouping the document tree into LaTeX files. List of tuples
# (source start file, target name, title,
#  author, documentclass [howto, manual, or own class]).
latex_documents = [
    (master_doc, 'mockturtle.tex', 'mockturtle Documentation',
     'EPFL LIS', 'manual'),
]


# -- Options for manual page output ---------------------------------------

# One entry per manual page. List of tuples
# (source start file, name, description, authors, manual section).
man_pages = [
    (master_doc, 'mockturtle', 'mockturtle Documentation',
     [author], 1)
]


# -- Options for Texinfo output -------------------------------------------

# Grouping the document tree into Texinfo files. List of tuples
# (source start file, target name, title, author,
#  dir menu entry, description, category)
texinfo_documents = [
    (master_doc, 'mockturtle', 'mockturtle Documentation',
     author, 'mockturtle', 'One line description of project.',
     'Miscellaneous'),
]

# -- Options for breathe --------------------------------------------------

import subprocess, os

read_the_docs_build = os.environ.get('READTHEDOCS', None) == 'True'

if read_the_docs_build:
    subprocess.call('doxygen Doxyfile', shell = True)

breathe_projects = {"mockturtle": "doxyxml/xml"}
breathe_default_project = "mockturtle"

# -- Custom directives ----------------------------------------------------

from docutils import nodes
from docutils.parsers.rst import Directive
from sphinx import addnodes
import xml.etree.ElementTree as ET

class DocOverviewTableDirective(Directive):
    has_content = True
    required_arguments = 1
    option_spec = {"column": str}

    def run(self):
        doc = ET.parse("doxyxml/xml/{}.xml".format(self.arguments[0]))

        table = nodes.table()
        tgroup = nodes.tgroup(cols = 2)

        tgroup += nodes.colspec(colwidth = 50)
        tgroup += nodes.colspec(colwidth = 50)

        # header
        colname = self.options.get('column', "Function")
        tgroup += nodes.thead('', nodes.row('', *[nodes.entry('', nodes.line(text = c)) for c in [colname, "Description"]]))

        # rows
        tbody = nodes.tbody()
        for target in self.content:
            for elem in doc.findall("./compounddef/sectiondef/memberdef/[name='%s']" % target):
                ref = nodes.reference('', target, internal = True)
                ref['refuri'] = '#{}'.format( elem.attrib["id"] )

                reft = nodes.paragraph()
                reft.extend([ref])

                func = nodes.entry('', reft)
                desc = nodes.entry('', nodes.line(text = elem.findtext("./briefdescription/para")))

                tbody += nodes.row('', func, desc)

        tgroup += tbody
        table += tgroup
        return [table]

def setup(app):
    app.add_directive('doc_overview_table', DocOverviewTableDirective)
