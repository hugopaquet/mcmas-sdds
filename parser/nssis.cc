/* A Bison parser, made by GNU Bison 2.5.  */

/* Skeleton implementation for Bison LALR(1) parsers in C++
   
      Copyright (C) 2002-2011 Free Software Foundation, Inc.
   
   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.
   
   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
   
   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.
   
   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */


/* First part of user declarations.  */


/* Line 293 of lalr1.cc  */
#line 39 "parser/nssis.cc"


#include "nssis.hh"

/* User implementation prologue.  */

/* Line 299 of lalr1.cc  */
#line 67 "parser/nssis_new.yy"

#include "mcmas-driver.hh"

  extern map < string, int > options;
  extern vector<string *> *string_table;
  extern vector<variable *> *variable_table;
  extern vector<bool_expression *> *logic_expression_table;
  extern vector<bool_expression *> *logic_expression_table1;
  extern map<string, basic_agent *> *is_agents;
  extern vector<basic_agent *> *agents;
  extern map<string, bool_expression *> *is_evaluation;
  extern bool_expression *is_istates;
  extern map<string, set<string> > *is_groups;
  extern vector<modal_formula> *is_formulae;
  extern vector<fairness_expression *> *is_fairness;

  extern int search_string_table(string *s);
  extern int search_variable_table(variable *v);
  extern int search_logic_expression_table(expression *e1, expression *e2);
  extern int search_logic_expression_table1(expression *e1, expression *e2);


/* Line 299 of lalr1.cc  */
#line 71 "parser/nssis.cc"

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* FIXME: INFRINGES ON USER NAME SPACE */
#   define YY_(msgid) dgettext ("bison-runtime", msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(msgid) msgid
# endif
#endif

/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

#define YYRHSLOC(Rhs, K) ((Rhs)[K])
#ifndef YYLLOC_DEFAULT
# define YYLLOC_DEFAULT(Current, Rhs, N)                               \
 do                                                                    \
   if (N)                                                              \
     {                                                                 \
       (Current).begin = YYRHSLOC (Rhs, 1).begin;                      \
       (Current).end   = YYRHSLOC (Rhs, N).end;                        \
     }                                                                 \
   else                                                                \
     {                                                                 \
       (Current).begin = (Current).end = YYRHSLOC (Rhs, 0).end;        \
     }                                                                 \
 while (false)
#endif

/* Suppress unused-variable warnings by "using" E.  */
#define YYUSE(e) ((void) (e))

/* Enable debugging if requested.  */
#if YYDEBUG

/* A pseudo ostream that takes yydebug_ into account.  */
# define YYCDEBUG if (yydebug_) (*yycdebug_)

# define YY_SYMBOL_PRINT(Title, Type, Value, Location)	\
do {							\
  if (yydebug_)						\
    {							\
      *yycdebug_ << Title << ' ';			\
      yy_symbol_print_ ((Type), (Value), (Location));	\
      *yycdebug_ << std::endl;				\
    }							\
} while (false)

# define YY_REDUCE_PRINT(Rule)		\
do {					\
  if (yydebug_)				\
    yy_reduce_print_ (Rule);		\
} while (false)

# define YY_STACK_PRINT()		\
do {					\
  if (yydebug_)				\
    yystack_print_ ();			\
} while (false)

#else /* !YYDEBUG */

# define YYCDEBUG if (false) std::cerr
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_REDUCE_PRINT(Rule)
# define YY_STACK_PRINT()

#endif /* !YYDEBUG */

#define yyerrok		(yyerrstatus_ = 0)
#define yyclearin	(yychar = yyempty_)

#define YYACCEPT	goto yyacceptlab
#define YYABORT		goto yyabortlab
#define YYERROR		goto yyerrorlab
#define YYRECOVERING()  (!!yyerrstatus_)


namespace yy {

/* Line 382 of lalr1.cc  */
#line 157 "parser/nssis.cc"

  /* Return YYSTR after stripping away unnecessary quotes and
     backslashes, so that it's suitable for yyerror.  The heuristic is
     that double-quoting is unnecessary unless the string contains an
     apostrophe, a comma, or backslash (other than backslash-backslash).
     YYSTR is taken from yytname.  */
  std::string
  mcmas_parser::yytnamerr_ (const char *yystr)
  {
    if (*yystr == '"')
      {
        std::string yyr = "";
        char const *yyp = yystr;

        for (;;)
          switch (*++yyp)
            {
            case '\'':
            case ',':
              goto do_not_strip_quotes;

            case '\\':
              if (*++yyp != '\\')
                goto do_not_strip_quotes;
              /* Fall through.  */
            default:
              yyr += *yyp;
              break;

            case '"':
              return yyr;
            }
      do_not_strip_quotes: ;
      }

    return yystr;
  }


  /// Build a parser object.
  mcmas_parser::mcmas_parser (mcmas_driver& driver_yyarg)
    :
#if YYDEBUG
      yydebug_ (false),
      yycdebug_ (&std::cerr),
#endif
      driver (driver_yyarg)
  {
  }

  mcmas_parser::~mcmas_parser ()
  {
  }

#if YYDEBUG
  /*--------------------------------.
  | Print this symbol on YYOUTPUT.  |
  `--------------------------------*/

  inline void
  mcmas_parser::yy_symbol_value_print_ (int yytype,
			   const semantic_type* yyvaluep, const location_type* yylocationp)
  {
    YYUSE (yylocationp);
    YYUSE (yyvaluep);
    switch (yytype)
      {
        case 72: /* "\"identifier\"" */

/* Line 449 of lalr1.cc  */
#line 225 "parser/nssis_new.yy"
	{ debug_stream () << *(yyvaluep->sval); };

/* Line 449 of lalr1.cc  */
#line 232 "parser/nssis.cc"
	break;
      case 73: /* "\"number\"" */

/* Line 449 of lalr1.cc  */
#line 265 "parser/nssis_new.yy"
	{ debug_stream () << (yyvaluep->ival); };

/* Line 449 of lalr1.cc  */
#line 241 "parser/nssis.cc"
	break;
       default:
	  break;
      }
  }


  void
  mcmas_parser::yy_symbol_print_ (int yytype,
			   const semantic_type* yyvaluep, const location_type* yylocationp)
  {
    *yycdebug_ << (yytype < yyntokens_ ? "token" : "nterm")
	       << ' ' << yytname_[yytype] << " ("
	       << *yylocationp << ": ";
    yy_symbol_value_print_ (yytype, yyvaluep, yylocationp);
    *yycdebug_ << ')';
  }
#endif

  void
  mcmas_parser::yydestruct_ (const char* yymsg,
			   int yytype, semantic_type* yyvaluep, location_type* yylocationp)
  {
    YYUSE (yylocationp);
    YYUSE (yymsg);
    YYUSE (yyvaluep);

    YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

    switch (yytype)
      {
        case 72: /* "\"identifier\"" */

/* Line 480 of lalr1.cc  */
#line 226 "parser/nssis_new.yy"
	{ delete (yyvaluep->sval); };

/* Line 480 of lalr1.cc  */
#line 280 "parser/nssis.cc"
	break;
      case 83: /* "obsvardef" */

/* Line 480 of lalr1.cc  */
#line 227 "parser/nssis_new.yy"
	{ delete (yyvaluep->map_vec_basictype); };

/* Line 480 of lalr1.cc  */
#line 289 "parser/nssis.cc"
	break;
      case 84: /* "varidlist" */

/* Line 480 of lalr1.cc  */
#line 228 "parser/nssis_new.yy"
	{ delete (yyvaluep->map_vec_basictype); };

/* Line 480 of lalr1.cc  */
#line 298 "parser/nssis.cc"
	break;
      case 85: /* "onevardef" */

/* Line 480 of lalr1.cc  */
#line 229 "parser/nssis_new.yy"
	{ delete (yyvaluep->_basictype); };

/* Line 480 of lalr1.cc  */
#line 307 "parser/nssis.cc"
	break;
      case 86: /* "enumlist" */

/* Line 480 of lalr1.cc  */
#line 230 "parser/nssis_new.yy"
	{ delete (yyvaluep->set_string); };

/* Line 480 of lalr1.cc  */
#line 316 "parser/nssis.cc"
	break;
      case 90: /* "envardef" */

/* Line 480 of lalr1.cc  */
#line 232 "parser/nssis_new.yy"
	{ delete (yyvaluep->map_vec_basictype); };

/* Line 480 of lalr1.cc  */
#line 325 "parser/nssis.cc"
	break;
      case 91: /* "vardef" */

/* Line 480 of lalr1.cc  */
#line 231 "parser/nssis_new.yy"
	{ delete (yyvaluep->map_vec_basictype); };

/* Line 480 of lalr1.cc  */
#line 334 "parser/nssis.cc"
	break;
      case 95: /* "reddef" */

/* Line 480 of lalr1.cc  */
#line 240 "parser/nssis_new.yy"
	{ delete (yyvaluep->_bool_expression); };

/* Line 480 of lalr1.cc  */
#line 343 "parser/nssis.cc"
	break;
      case 97: /* "rboolcond" */

/* Line 480 of lalr1.cc  */
#line 239 "parser/nssis_new.yy"
	{ delete (yyvaluep->_bool_expression); };

/* Line 480 of lalr1.cc  */
#line 352 "parser/nssis.cc"
	break;
      case 100: /* "envevdef" */

/* Line 480 of lalr1.cc  */
#line 233 "parser/nssis_new.yy"
	{ delete (yyvaluep->vector_evolution_line); };

/* Line 480 of lalr1.cc  */
#line 361 "parser/nssis.cc"
	break;
      case 101: /* "envevdeflist" */

/* Line 480 of lalr1.cc  */
#line 234 "parser/nssis_new.yy"
	{ delete (yyvaluep->vector_evolution_line); };

/* Line 480 of lalr1.cc  */
#line 370 "parser/nssis.cc"
	break;
      case 102: /* "envevline" */

/* Line 480 of lalr1.cc  */
#line 235 "parser/nssis_new.yy"
	{ delete (yyvaluep->_evolution_line); };

/* Line 480 of lalr1.cc  */
#line 379 "parser/nssis.cc"
	break;
      case 103: /* "boolresult" */

/* Line 480 of lalr1.cc  */
#line 236 "parser/nssis_new.yy"
	{ delete (yyvaluep->vector_assignment); };

/* Line 480 of lalr1.cc  */
#line 388 "parser/nssis.cc"
	break;
      case 108: /* "agent" */

/* Line 480 of lalr1.cc  */
#line 245 "parser/nssis_new.yy"
	{ delete (yyvaluep->_basic_agent); };

/* Line 480 of lalr1.cc  */
#line 397 "parser/nssis.cc"
	break;
      case 115: /* "enactiondef" */

/* Line 480 of lalr1.cc  */
#line 247 "parser/nssis_new.yy"
	{ delete (yyvaluep->set_string); };

/* Line 480 of lalr1.cc  */
#line 406 "parser/nssis.cc"
	break;
      case 116: /* "actiondef" */

/* Line 480 of lalr1.cc  */
#line 246 "parser/nssis_new.yy"
	{ delete (yyvaluep->set_string); };

/* Line 480 of lalr1.cc  */
#line 415 "parser/nssis.cc"
	break;
      case 117: /* "actionidlist" */

/* Line 480 of lalr1.cc  */
#line 248 "parser/nssis_new.yy"
	{ delete (yyvaluep->set_string); };

/* Line 480 of lalr1.cc  */
#line 424 "parser/nssis.cc"
	break;
      case 120: /* "enprotdef" */

/* Line 480 of lalr1.cc  */
#line 250 "parser/nssis_new.yy"
	{ delete (yyvaluep->vector_protocol_line); };

/* Line 480 of lalr1.cc  */
#line 433 "parser/nssis.cc"
	break;
      case 121: /* "protdef" */

/* Line 480 of lalr1.cc  */
#line 249 "parser/nssis_new.yy"
	{ delete (yyvaluep->vector_protocol_line); };

/* Line 480 of lalr1.cc  */
#line 442 "parser/nssis.cc"
	break;
      case 123: /* "protdeflist" */

/* Line 480 of lalr1.cc  */
#line 251 "parser/nssis_new.yy"
	{ delete (yyvaluep->vector_protocol_line); };

/* Line 480 of lalr1.cc  */
#line 451 "parser/nssis.cc"
	break;
      case 127: /* "protline" */

/* Line 480 of lalr1.cc  */
#line 252 "parser/nssis_new.yy"
	{ delete (yyvaluep->_protocol_line); };

/* Line 480 of lalr1.cc  */
#line 460 "parser/nssis.cc"
	break;
      case 129: /* "enabledidlist" */

/* Line 480 of lalr1.cc  */
#line 253 "parser/nssis_new.yy"
	{ delete (yyvaluep->set_string); };

/* Line 480 of lalr1.cc  */
#line 469 "parser/nssis.cc"
	break;
      case 130: /* "evdef" */

/* Line 480 of lalr1.cc  */
#line 254 "parser/nssis_new.yy"
	{ delete (yyvaluep->vector_evolution_line); };

/* Line 480 of lalr1.cc  */
#line 478 "parser/nssis.cc"
	break;
      case 131: /* "evdeflist" */

/* Line 480 of lalr1.cc  */
#line 255 "parser/nssis_new.yy"
	{ delete (yyvaluep->vector_evolution_line); };

/* Line 480 of lalr1.cc  */
#line 487 "parser/nssis.cc"
	break;
      case 132: /* "evline" */

/* Line 480 of lalr1.cc  */
#line 256 "parser/nssis_new.yy"
	{ delete (yyvaluep->_evolution_line); };

/* Line 480 of lalr1.cc  */
#line 496 "parser/nssis.cc"
	break;
      case 134: /* "lboolcond" */

/* Line 480 of lalr1.cc  */
#line 237 "parser/nssis_new.yy"
	{ delete (yyvaluep->_bool_expression); };

/* Line 480 of lalr1.cc  */
#line 505 "parser/nssis.cc"
	break;
      case 156: /* "eboolcond" */

/* Line 480 of lalr1.cc  */
#line 238 "parser/nssis_new.yy"
	{ delete (yyvaluep->_bool_expression); };

/* Line 480 of lalr1.cc  */
#line 514 "parser/nssis.cc"
	break;
      case 158: /* "gboolcond" */

/* Line 480 of lalr1.cc  */
#line 257 "parser/nssis_new.yy"
	{ delete (yyvaluep->_bool_expression); };

/* Line 480 of lalr1.cc  */
#line 523 "parser/nssis.cc"
	break;
      case 159: /* "varvalue1" */

/* Line 480 of lalr1.cc  */
#line 241 "parser/nssis_new.yy"
	{ delete (yyvaluep->_expression); };

/* Line 480 of lalr1.cc  */
#line 532 "parser/nssis.cc"
	break;
      case 160: /* "boolvalue" */

/* Line 480 of lalr1.cc  */
#line 258 "parser/nssis_new.yy"
	{ delete (yyvaluep->_bool_value); };

/* Line 480 of lalr1.cc  */
#line 541 "parser/nssis.cc"
	break;
      case 161: /* "varvalue2" */

/* Line 480 of lalr1.cc  */
#line 242 "parser/nssis_new.yy"
	{ delete (yyvaluep->_expression); };

/* Line 480 of lalr1.cc  */
#line 550 "parser/nssis.cc"
	break;
      case 162: /* "varvalue3" */

/* Line 480 of lalr1.cc  */
#line 243 "parser/nssis_new.yy"
	{ delete (yyvaluep->_expression); };

/* Line 480 of lalr1.cc  */
#line 559 "parser/nssis.cc"
	break;
      case 163: /* "varvalue4" */

/* Line 480 of lalr1.cc  */
#line 244 "parser/nssis_new.yy"
	{ delete (yyvaluep->_expression); };

/* Line 480 of lalr1.cc  */
#line 568 "parser/nssis.cc"
	break;
      case 168: /* "evaboolcond" */

/* Line 480 of lalr1.cc  */
#line 259 "parser/nssis_new.yy"
	{ delete (yyvaluep->_bool_expression); };

/* Line 480 of lalr1.cc  */
#line 577 "parser/nssis.cc"
	break;
      case 172: /* "isboolcond" */

/* Line 480 of lalr1.cc  */
#line 260 "parser/nssis_new.yy"
	{ delete (yyvaluep->_bool_expression); };

/* Line 480 of lalr1.cc  */
#line 586 "parser/nssis.cc"
	break;
      case 179: /* "namelist" */

/* Line 480 of lalr1.cc  */
#line 261 "parser/nssis_new.yy"
	{ delete (yyvaluep->set_string); };

/* Line 480 of lalr1.cc  */
#line 595 "parser/nssis.cc"
	break;
      case 180: /* "agentname" */

/* Line 480 of lalr1.cc  */
#line 262 "parser/nssis_new.yy"
	{ delete (yyvaluep->sval); };

/* Line 480 of lalr1.cc  */
#line 604 "parser/nssis.cc"
	break;
      case 197: /* "formula" */

/* Line 480 of lalr1.cc  */
#line 263 "parser/nssis_new.yy"
	{ delete (yyvaluep->_modal_formula); };

/* Line 480 of lalr1.cc  */
#line 613 "parser/nssis.cc"
	break;

	default:
	  break;
      }
  }

  void
  mcmas_parser::yypop_ (unsigned int n)
  {
    yystate_stack_.pop (n);
    yysemantic_stack_.pop (n);
    yylocation_stack_.pop (n);
  }

#if YYDEBUG
  std::ostream&
  mcmas_parser::debug_stream () const
  {
    return *yycdebug_;
  }

  void
  mcmas_parser::set_debug_stream (std::ostream& o)
  {
    yycdebug_ = &o;
  }


  mcmas_parser::debug_level_type
  mcmas_parser::debug_level () const
  {
    return yydebug_;
  }

  void
  mcmas_parser::set_debug_level (debug_level_type l)
  {
    yydebug_ = l;
  }
#endif

  inline bool
  mcmas_parser::yy_pact_value_is_default_ (int yyvalue)
  {
    return yyvalue == yypact_ninf_;
  }

  inline bool
  mcmas_parser::yy_table_value_is_error_ (int yyvalue)
  {
    return yyvalue == yytable_ninf_;
  }

  int
  mcmas_parser::parse ()
  {
    /// Lookahead and lookahead in internal form.
    int yychar = yyempty_;
    int yytoken = 0;

    /* State.  */
    int yyn;
    int yylen = 0;
    int yystate = 0;

    /* Error handling.  */
    int yynerrs_ = 0;
    int yyerrstatus_ = 0;

    /// Semantic value of the lookahead.
    semantic_type yylval;
    /// Location of the lookahead.
    location_type yylloc;
    /// The locations where the error started and ended.
    location_type yyerror_range[3];

    /// $$.
    semantic_type yyval;
    /// @$.
    location_type yyloc;

    int yyresult;

    YYCDEBUG << "Starting parse" << std::endl;


    /* User initialization code.  */
    
/* Line 565 of lalr1.cc  */
#line 29 "parser/nssis_new.yy"
{
  // Initialize the initial location.
  yylloc.begin.filename = yylloc.end.filename = &driver.file;
}

/* Line 565 of lalr1.cc  */
#line 711 "parser/nssis.cc"

    /* Initialize the stacks.  The initial state will be pushed in
       yynewstate, since the latter expects the semantical and the
       location values to have been already stored, initialize these
       stacks with a primary value.  */
    yystate_stack_ = state_stack_type (0);
    yysemantic_stack_ = semantic_stack_type (0);
    yylocation_stack_ = location_stack_type (0);
    yysemantic_stack_.push (yylval);
    yylocation_stack_.push (yylloc);

    /* New state.  */
  yynewstate:
    yystate_stack_.push (yystate);
    YYCDEBUG << "Entering state " << yystate << std::endl;

    /* Accept?  */
    if (yystate == yyfinal_)
      goto yyacceptlab;

    goto yybackup;

    /* Backup.  */
  yybackup:

    /* Try to take a decision without lookahead.  */
    yyn = yypact_[yystate];
    if (yy_pact_value_is_default_ (yyn))
      goto yydefault;

    /* Read a lookahead token.  */
    if (yychar == yyempty_)
      {
	YYCDEBUG << "Reading a token: ";
	yychar = yylex (&yylval, &yylloc, driver);
      }


    /* Convert token to internal form.  */
    if (yychar <= yyeof_)
      {
	yychar = yytoken = yyeof_;
	YYCDEBUG << "Now at end of input." << std::endl;
      }
    else
      {
	yytoken = yytranslate_ (yychar);
	YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
      }

    /* If the proper action on seeing token YYTOKEN is to reduce or to
       detect an error, take that action.  */
    yyn += yytoken;
    if (yyn < 0 || yylast_ < yyn || yycheck_[yyn] != yytoken)
      goto yydefault;

    /* Reduce or error.  */
    yyn = yytable_[yyn];
    if (yyn <= 0)
      {
	if (yy_table_value_is_error_ (yyn))
	  goto yyerrlab;
	yyn = -yyn;
	goto yyreduce;
      }

    /* Shift the lookahead token.  */
    YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);

    /* Discard the token being shifted.  */
    yychar = yyempty_;

    yysemantic_stack_.push (yylval);
    yylocation_stack_.push (yylloc);

    /* Count tokens shifted since error; after three, turn off error
       status.  */
    if (yyerrstatus_)
      --yyerrstatus_;

    yystate = yyn;
    goto yynewstate;

  /*-----------------------------------------------------------.
  | yydefault -- do the default action for the current state.  |
  `-----------------------------------------------------------*/
  yydefault:
    yyn = yydefact_[yystate];
    if (yyn == 0)
      goto yyerrlab;
    goto yyreduce;

  /*-----------------------------.
  | yyreduce -- Do a reduction.  |
  `-----------------------------*/
  yyreduce:
    yylen = yyr2_[yyn];
    /* If YYLEN is nonzero, implement the default value of the action:
       `$$ = $1'.  Otherwise, use the top of the stack.

       Otherwise, the following line sets YYVAL to garbage.
       This behavior is undocumented and Bison
       users should not rely upon it.  */
    if (yylen)
      yyval = yysemantic_stack_[yylen - 1];
    else
      yyval = yysemantic_stack_[0];

    {
      slice<location_type, location_stack_type> slice (yylocation_stack_, yylen);
      YYLLOC_DEFAULT (yyloc, slice, yylen);
    }
    YY_REDUCE_PRINT (yyn);
    switch (yyn)
      {
	  case 4:

/* Line 690 of lalr1.cc  */
#line 273 "parser/nssis_new.yy"
    {
    options["smv"] = 0;
 }
    break;

  case 5:

/* Line 690 of lalr1.cc  */
#line 276 "parser/nssis_new.yy"
    {
    options["smv"] = 1;
 }
    break;

  case 6:

/* Line 690 of lalr1.cc  */
#line 279 "parser/nssis_new.yy"
    {
  driver.syntax_error = true;
 }
    break;

  case 11:

/* Line 690 of lalr1.cc  */
#line 288 "parser/nssis_new.yy"
    {
  basic_agent *env = new basic_agent((*string_table)[0], NULL, new map<string, basictype *>, new vector<basictype *>,
				     new map<string, basictype *>, new vector<basictype *>, NULL, new set<string>, 
				     new vector<protocol_line*>, new vector<evolution_line *>);
  (*is_agents)["Environment"] = env;
  agents->insert(agents->begin(), env);
 }
    break;

  case 12:

/* Line 690 of lalr1.cc  */
#line 295 "parser/nssis_new.yy"
    {
  basic_agent *env = new basic_agent((*string_table)[0], NULL, new map<string, basictype *>, new vector<basictype *>, 
				     new map<string, basictype *>, new vector<basictype *>, NULL, new set<string>, 
				     new vector<protocol_line*>, new vector<evolution_line *>);
  (*is_agents)["Environment"] = env;
  agents->insert(agents->begin(), env);
 }
    break;

  case 13:

/* Line 690 of lalr1.cc  */
#line 302 "parser/nssis_new.yy"
    {
  basic_agent *env = new basic_agent((*string_table)[0], NULL, new map<string, basictype *>, new vector<basictype *>, 
				     new map<string, basictype *>, new vector<basictype *>, NULL, new set<string>, 
				     new vector<protocol_line*>, new vector<evolution_line *>);
  (*is_agents)["Environment"] = env;
  agents->insert(agents->begin(), env);
 }
    break;

  case 14:

/* Line 690 of lalr1.cc  */
#line 309 "parser/nssis_new.yy"
    {
  basic_agent *env = new basic_agent((*string_table)[0], NULL, new map<string, basictype *>, new vector<basictype *>, 
				     new map<string, basictype *>, new vector<basictype *>, NULL, new set<string>, 
				     new vector<protocol_line*>, new vector<evolution_line *>);
  (*is_agents)["Environment"] = env;
  agents->insert(agents->begin(), env);
 }
    break;

  case 15:

/* Line 690 of lalr1.cc  */
#line 319 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 16:

/* Line 690 of lalr1.cc  */
#line 322 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 17:

/* Line 690 of lalr1.cc  */
#line 326 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 18:

/* Line 690 of lalr1.cc  */
#line 330 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 19:

/* Line 690 of lalr1.cc  */
#line 334 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 20:

/* Line 690 of lalr1.cc  */
#line 337 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 21:

/* Line 690 of lalr1.cc  */
#line 341 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 22:

/* Line 690 of lalr1.cc  */
#line 345 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 23:

/* Line 690 of lalr1.cc  */
#line 350 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(8) - (1)].ival)==1 && (yysemantic_stack_[(8) - (2)].map_vec_basictype)!=NULL && (yysemantic_stack_[(8) - (3)].map_vec_basictype)!=NULL && (yysemantic_stack_[(8) - (5)].set_string)!=NULL && (yysemantic_stack_[(8) - (6)].vector_protocol_line)!=NULL && (yysemantic_stack_[(8) - (7)].vector_evolution_line)!=NULL && (yysemantic_stack_[(8) - (8)].ival)==1) { // redstates is NULL if no red state at all
    basic_agent *env = new basic_agent((*string_table)[0], NULL, (yysemantic_stack_[(8) - (2)].map_vec_basictype)->first, (yysemantic_stack_[(8) - (2)].map_vec_basictype)->second, (yysemantic_stack_[(8) - (3)].map_vec_basictype)->first, (yysemantic_stack_[(8) - (3)].map_vec_basictype)->second, (yysemantic_stack_[(8) - (4)]._bool_expression), (yysemantic_stack_[(8) - (5)].set_string), (yysemantic_stack_[(8) - (6)].vector_protocol_line), (yysemantic_stack_[(8) - (7)].vector_evolution_line));
    (*is_agents)["Environment"] = env;
    agents->push_back(env);
  }
 }
    break;

  case 24:

/* Line 690 of lalr1.cc  */
#line 357 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(7) - (1)].ival)==1 && (yysemantic_stack_[(7) - (2)].map_vec_basictype)!=NULL && (yysemantic_stack_[(7) - (3)].map_vec_basictype)!=NULL && (yysemantic_stack_[(7) - (4)].set_string)!=NULL && (yysemantic_stack_[(7) - (5)].vector_protocol_line)!=NULL && (yysemantic_stack_[(7) - (6)].vector_evolution_line)!=NULL && (yysemantic_stack_[(7) - (7)].ival)==1) { // redstates is NULL if no red state at all
    basic_agent *env = new basic_agent((*string_table)[0], NULL, (yysemantic_stack_[(7) - (2)].map_vec_basictype)->first, (yysemantic_stack_[(7) - (2)].map_vec_basictype)->second, (yysemantic_stack_[(7) - (3)].map_vec_basictype)->first, (yysemantic_stack_[(7) - (3)].map_vec_basictype)->second, NULL, (yysemantic_stack_[(7) - (4)].set_string), (yysemantic_stack_[(7) - (5)].vector_protocol_line), (yysemantic_stack_[(7) - (6)].vector_evolution_line));
    (*is_agents)["Environment"] = env;
    agents->push_back(env);
  }
 }
    break;

  case 25:

/* Line 690 of lalr1.cc  */
#line 364 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(7) - (1)].ival)==1 && (yysemantic_stack_[(7) - (2)].map_vec_basictype)!=NULL && (yysemantic_stack_[(7) - (4)].set_string)!=NULL && (yysemantic_stack_[(7) - (5)].vector_protocol_line)!=NULL && (yysemantic_stack_[(7) - (6)].vector_evolution_line)!=NULL && (yysemantic_stack_[(7) - (7)].ival)==1) { // redstates is NULL if no red state at all
    basic_agent *env = new basic_agent((*string_table)[0], NULL, new map<string, basictype *>, new vector<basictype *>, (yysemantic_stack_[(7) - (2)].map_vec_basictype)->first, (yysemantic_stack_[(7) - (2)].map_vec_basictype)->second, (yysemantic_stack_[(7) - (3)]._bool_expression), (yysemantic_stack_[(7) - (4)].set_string), (yysemantic_stack_[(7) - (5)].vector_protocol_line), (yysemantic_stack_[(7) - (6)].vector_evolution_line));
    (*is_agents)["Environment"] = env;
    agents->push_back(env);
  }
 }
    break;

  case 26:

/* Line 690 of lalr1.cc  */
#line 371 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(6) - (1)].ival)==1 && (yysemantic_stack_[(6) - (2)].map_vec_basictype)!=NULL && (yysemantic_stack_[(6) - (3)].set_string)!=NULL && (yysemantic_stack_[(6) - (4)].vector_protocol_line)!=NULL && (yysemantic_stack_[(6) - (5)].vector_evolution_line)!=NULL && (yysemantic_stack_[(6) - (6)].ival)==1) { // redstates is NULL if no red state at all
    basic_agent *env = new basic_agent((*string_table)[0], NULL, new map<string, basictype *>, new vector<basictype *>, (yysemantic_stack_[(6) - (2)].map_vec_basictype)->first, (yysemantic_stack_[(6) - (2)].map_vec_basictype)->second, NULL, (yysemantic_stack_[(6) - (3)].set_string), (yysemantic_stack_[(6) - (4)].vector_protocol_line), (yysemantic_stack_[(6) - (5)].vector_evolution_line));
    (*is_agents)["Environment"] = env;
    agents->push_back(env);
  }
 }
    break;

  case 27:

/* Line 690 of lalr1.cc  */
#line 378 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(7) - (1)].ival)==1 && (yysemantic_stack_[(7) - (2)].map_vec_basictype)!=NULL && (yysemantic_stack_[(7) - (4)].set_string)!=NULL && (yysemantic_stack_[(7) - (5)].vector_protocol_line)!=NULL && (yysemantic_stack_[(7) - (6)].vector_evolution_line)!=NULL && (yysemantic_stack_[(7) - (7)].ival)==1) { // redstates is NULL if no red state at all
    basic_agent *env = new basic_agent((*string_table)[0], NULL, (yysemantic_stack_[(7) - (2)].map_vec_basictype)->first, (yysemantic_stack_[(7) - (2)].map_vec_basictype)->second, new map<string, basictype *>, new vector<basictype *>, (yysemantic_stack_[(7) - (3)]._bool_expression), (yysemantic_stack_[(7) - (4)].set_string), (yysemantic_stack_[(7) - (5)].vector_protocol_line), (yysemantic_stack_[(7) - (6)].vector_evolution_line));
    (*is_agents)["Environment"] = env;
    agents->push_back(env);
  }
 }
    break;

  case 28:

/* Line 690 of lalr1.cc  */
#line 385 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(6) - (1)].ival)==1 && (yysemantic_stack_[(6) - (2)].map_vec_basictype)!=NULL && (yysemantic_stack_[(6) - (3)].set_string)!=NULL && (yysemantic_stack_[(6) - (4)].vector_protocol_line)!=NULL && (yysemantic_stack_[(6) - (5)].vector_evolution_line)!=NULL && (yysemantic_stack_[(6) - (6)].ival)==1) { // redstates is NULL if no red state at all
    basic_agent *env = new basic_agent((*string_table)[0], NULL, (yysemantic_stack_[(6) - (2)].map_vec_basictype)->first, (yysemantic_stack_[(6) - (2)].map_vec_basictype)->second, new map<string, basictype *>, new vector<basictype *>, NULL, (yysemantic_stack_[(6) - (3)].set_string), (yysemantic_stack_[(6) - (4)].vector_protocol_line), (yysemantic_stack_[(6) - (5)].vector_evolution_line));
    (*is_agents)["Environment"] = env;
    agents->push_back(env);
  }
 }
    break;

  case 29:

/* Line 690 of lalr1.cc  */
#line 392 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(6) - (1)].ival)==1 && (yysemantic_stack_[(6) - (3)].set_string)!=NULL && (yysemantic_stack_[(6) - (4)].vector_protocol_line)!=NULL && (yysemantic_stack_[(6) - (5)].vector_evolution_line)!=NULL && (yysemantic_stack_[(6) - (6)].ival)==1) { // redstates is NULL if no red state at all
    basic_agent *env = new basic_agent((*string_table)[0], NULL, new map<string, basictype *>, new vector<basictype *>, 
				       new map<string, basictype *>, new vector<basictype *>, (yysemantic_stack_[(6) - (2)]._bool_expression), (yysemantic_stack_[(6) - (3)].set_string), (yysemantic_stack_[(6) - (4)].vector_protocol_line), (yysemantic_stack_[(6) - (5)].vector_evolution_line));
    (*is_agents)["Environment"] = env;
    agents->push_back(env);
  }
 }
    break;

  case 30:

/* Line 690 of lalr1.cc  */
#line 400 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(5) - (1)].ival)==1 && (yysemantic_stack_[(5) - (2)].set_string)!=NULL && (yysemantic_stack_[(5) - (3)].vector_protocol_line)!=NULL && (yysemantic_stack_[(5) - (4)].vector_evolution_line)!=NULL && (yysemantic_stack_[(5) - (5)].ival)==1) { // redstates is NULL if no red state at all
    basic_agent *env = new basic_agent((*string_table)[0], NULL, new map<string, basictype *>, new vector<basictype *>, 
				       new map<string, basictype *>, new vector<basictype *>, NULL, (yysemantic_stack_[(5) - (2)].set_string), (yysemantic_stack_[(5) - (3)].vector_protocol_line), (yysemantic_stack_[(5) - (4)].vector_evolution_line));
    (*is_agents)["Environment"] = env;
    agents->push_back(env);
  }
 }
    break;

  case 31:

/* Line 690 of lalr1.cc  */
#line 408 "parser/nssis_new.yy"
    {
  driver.syntax_error = true;
  }
    break;

  case 32:

/* Line 690 of lalr1.cc  */
#line 413 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 33:

/* Line 690 of lalr1.cc  */
#line 416 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 34:

/* Line 690 of lalr1.cc  */
#line 420 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 35:

/* Line 690 of lalr1.cc  */
#line 424 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 36:

/* Line 690 of lalr1.cc  */
#line 428 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 37:

/* Line 690 of lalr1.cc  */
#line 431 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 38:

/* Line 690 of lalr1.cc  */
#line 435 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 39:

/* Line 690 of lalr1.cc  */
#line 439 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 40:

/* Line 690 of lalr1.cc  */
#line 443 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].ival)==1 && (yysemantic_stack_[(3) - (3)].ival)==1)
    (yyval.map_vec_basictype) = (yysemantic_stack_[(3) - (2)].map_vec_basictype);
  else
    (yyval.map_vec_basictype) = NULL;
 }
    break;

  case 41:

/* Line 690 of lalr1.cc  */
#line 449 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (1)].ival)==1 && (yysemantic_stack_[(2) - (2)].ival)==1) {
    map<string, basictype *>* a = new map<string, basictype *>;
    vector<basictype *>* b = new vector<basictype *>;
    (yyval.map_vec_basictype) = new pair<map<string, basictype *>*, vector<basictype *>* >(a, b);
  } else
    (yyval.map_vec_basictype) = NULL;
 }
    break;

  case 42:

/* Line 690 of lalr1.cc  */
#line 457 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (1)]._basictype)!=NULL) {
    map<string, basictype *>* a = new map<string, basictype *>;
    vector<basictype *>* b = new vector<basictype *>;
    (yyval.map_vec_basictype) = new pair<map<string, basictype *>*, vector<basictype *>* >(a, b);
    (*a)[(yysemantic_stack_[(2) - (1)]._basictype)->get_name()] = (yysemantic_stack_[(2) - (1)]._basictype);
    b->push_back((yysemantic_stack_[(2) - (1)]._basictype));
  } else
    (yyval.map_vec_basictype) = NULL;
 }
    break;

  case 43:

/* Line 690 of lalr1.cc  */
#line 467 "parser/nssis_new.yy"
    {
  (yyval.map_vec_basictype) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(2) - (1)]._basictype));
 }
    break;

  case 44:

/* Line 690 of lalr1.cc  */
#line 472 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].map_vec_basictype)!=NULL && (yysemantic_stack_[(3) - (2)]._basictype)!=NULL) {
    if((yysemantic_stack_[(3) - (1)].map_vec_basictype)->first->find((yysemantic_stack_[(3) - (2)]._basictype)->get_name()) != (yysemantic_stack_[(3) - (1)].map_vec_basictype)->first->end()) {
			if (options["quiet"] == 0)			
				cout << "warning: type " << (yysemantic_stack_[(3) - (2)]._basictype)->get_name() << " has already been defined." << endl;
    } else { 
      (*((yysemantic_stack_[(3) - (1)].map_vec_basictype)->first))[(yysemantic_stack_[(3) - (2)]._basictype)->get_name()] = (yysemantic_stack_[(3) - (2)]._basictype);
      (yysemantic_stack_[(3) - (1)].map_vec_basictype)->second->push_back((yysemantic_stack_[(3) - (2)]._basictype));
      (yyval.map_vec_basictype) = (yysemantic_stack_[(3) - (1)].map_vec_basictype);
    }
  } else
    (yyval.map_vec_basictype) = NULL;
 }
    break;

  case 45:

/* Line 690 of lalr1.cc  */
#line 485 "parser/nssis_new.yy"
    {
  (yyval.map_vec_basictype) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)].map_vec_basictype));
  USE((yysemantic_stack_[(3) - (2)]._basictype));
 }
    break;

  case 46:

/* Line 690 of lalr1.cc  */
#line 491 "parser/nssis_new.yy"
    {
  (yyval.map_vec_basictype) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 47:

/* Line 690 of lalr1.cc  */
#line 496 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].sval)!=NULL) {
    int i = search_string_table((yysemantic_stack_[(3) - (1)].sval));
    if(i>=0) {
      (yyval._basictype) = new basictype((*string_table)[i]);
      free((yysemantic_stack_[(3) - (1)].sval));
    } else {
      (yyval._basictype) = new basictype((yysemantic_stack_[(3) - (1)].sval));
      string_table->push_back((yysemantic_stack_[(3) - (1)].sval));
    }
  } else
    (yyval._basictype) = NULL;
 }
    break;

  case 48:

/* Line 690 of lalr1.cc  */
#line 509 "parser/nssis_new.yy"
    {
  (yyval._basictype) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)].sval));
 }
    break;

  case 49:

/* Line 690 of lalr1.cc  */
#line 514 "parser/nssis_new.yy"
    {
  (yyval._basictype) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)].sval));
 }
    break;

  case 50:

/* Line 690 of lalr1.cc  */
#line 519 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(5) - (1)].sval)!=NULL) {
    if((yysemantic_stack_[(5) - (3)].ival)>(yysemantic_stack_[(5) - (5)].ival))
      cout << "Error: the lower bound " << (yysemantic_stack_[(5) - (3)].ival) << " is greater than the upper bound " << (yysemantic_stack_[(5) - (5)].ival) << endl;
    int i = search_string_table((yysemantic_stack_[(5) - (1)].sval));
    if(i>=0) {
      (yyval._basictype) = new rangedint((*string_table)[i], (yysemantic_stack_[(5) - (3)].ival), (yysemantic_stack_[(5) - (5)].ival));
      free((yysemantic_stack_[(5) - (1)].sval));
    } else {
      (yyval._basictype) = new rangedint((yysemantic_stack_[(5) - (1)].sval), (yysemantic_stack_[(5) - (3)].ival), (yysemantic_stack_[(5) - (5)].ival));
      string_table->push_back((yysemantic_stack_[(5) - (1)].sval));
    }
  }
  else
    (yyval._basictype) = NULL;
 }
    break;

  case 51:

/* Line 690 of lalr1.cc  */
#line 535 "parser/nssis_new.yy"
    {
  (yyval._basictype) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (1)].sval));
 }
    break;

  case 52:

/* Line 690 of lalr1.cc  */
#line 540 "parser/nssis_new.yy"
    {
  (yyval._basictype) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (1)].sval));
 }
    break;

  case 53:

/* Line 690 of lalr1.cc  */
#line 545 "parser/nssis_new.yy"
    {
  (yyval._basictype) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (1)].sval));
 }
    break;

  case 54:

/* Line 690 of lalr1.cc  */
#line 550 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(5) - (1)].sval)!=NULL && (yysemantic_stack_[(5) - (4)].set_string)!=NULL) {
    int i = search_string_table((yysemantic_stack_[(5) - (1)].sval));
    if(i>=0) {
      (yyval._basictype) = new enumerate((*string_table)[i], (yysemantic_stack_[(5) - (4)].set_string));
      free((yysemantic_stack_[(5) - (1)].sval));
    } else {
      (yyval._basictype) = new enumerate((yysemantic_stack_[(5) - (1)].sval), (yysemantic_stack_[(5) - (4)].set_string));
      string_table->push_back((yysemantic_stack_[(5) - (1)].sval));
    }
  } else
    (yyval._basictype) = NULL;
 }
    break;

  case 55:

/* Line 690 of lalr1.cc  */
#line 563 "parser/nssis_new.yy"
    {
  (yyval._basictype) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(4) - (1)].sval));
  USE((yysemantic_stack_[(4) - (3)].set_string));
 }
    break;

  case 56:

/* Line 690 of lalr1.cc  */
#line 569 "parser/nssis_new.yy"
    {
  (yyval._basictype) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (1)].sval));
  USE((yysemantic_stack_[(5) - (4)].set_string));
 }
    break;

  case 57:

/* Line 690 of lalr1.cc  */
#line 575 "parser/nssis_new.yy"
    {
  (yyval._basictype) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(4) - (1)].sval));
  USE((yysemantic_stack_[(4) - (3)].set_string));
 }
    break;

  case 58:

/* Line 690 of lalr1.cc  */
#line 581 "parser/nssis_new.yy"
    {
  (yyval._basictype) = NULL;
  driver.syntax_error = true;
 }
    break;

  case 59:

/* Line 690 of lalr1.cc  */
#line 585 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(1) - (1)].sval)!=NULL) {
    (yyval.set_string) = new set<string>;
    (yyval.set_string)->insert(*(yysemantic_stack_[(1) - (1)].sval));
    free ((yysemantic_stack_[(1) - (1)].sval));
  } else
    (yyval.set_string) = NULL;
 }
    break;

  case 60:

/* Line 690 of lalr1.cc  */
#line 593 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].set_string)!=NULL && (yysemantic_stack_[(3) - (3)].sval)!=NULL) {
    pair<set<string>::iterator, bool> ret = (yysemantic_stack_[(3) - (1)].set_string)->insert(*(yysemantic_stack_[(3) - (3)].sval));
    if(!ret.second && options["quiet"] == 0)
      cout << "warning: " << *(yysemantic_stack_[(3) - (3)].sval) << " has been defined for the enum type." << endl;
    (yyval.set_string) = (yysemantic_stack_[(3) - (1)].set_string);
    free ((yysemantic_stack_[(3) - (3)].sval));
  } else
    (yyval.set_string) = NULL;
	USE((yysemantic_stack_[(3) - (1)].set_string));
 }
    break;

  case 61:

/* Line 690 of lalr1.cc  */
#line 604 "parser/nssis_new.yy"
    {
  (yyval.set_string) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)].set_string));
  USE((yysemantic_stack_[(3) - (3)].sval));
 }
    break;

  case 62:

/* Line 690 of lalr1.cc  */
#line 610 "parser/nssis_new.yy"
    {
  (yyval.set_string) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 63:

/* Line 690 of lalr1.cc  */
#line 614 "parser/nssis_new.yy"
    {
  (yyval.ival) = (yysemantic_stack_[(1) - (1)].ival);
 }
    break;

  case 64:

/* Line 690 of lalr1.cc  */
#line 617 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0-(yysemantic_stack_[(2) - (2)].ival);
 }
    break;

  case 65:

/* Line 690 of lalr1.cc  */
#line 620 "parser/nssis_new.yy"
    {
  (yyval.ival) = -1;
  driver.syntax_error = true;
 }
    break;

  case 66:

/* Line 690 of lalr1.cc  */
#line 624 "parser/nssis_new.yy"
    {
  (yyval.ival) = -1;
  driver.syntax_error = true;
  }
    break;

  case 67:

/* Line 690 of lalr1.cc  */
#line 630 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 68:

/* Line 690 of lalr1.cc  */
#line 633 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 69:

/* Line 690 of lalr1.cc  */
#line 637 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 70:

/* Line 690 of lalr1.cc  */
#line 641 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 71:

/* Line 690 of lalr1.cc  */
#line 645 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 72:

/* Line 690 of lalr1.cc  */
#line 648 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 73:

/* Line 690 of lalr1.cc  */
#line 652 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 74:

/* Line 690 of lalr1.cc  */
#line 656 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 75:

/* Line 690 of lalr1.cc  */
#line 660 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].ival)==1 && (yysemantic_stack_[(3) - (3)].ival)==1)
    (yyval.map_vec_basictype) = (yysemantic_stack_[(3) - (2)].map_vec_basictype);
  else
    (yyval.map_vec_basictype) = NULL;
 }
    break;

  case 76:

/* Line 690 of lalr1.cc  */
#line 666 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (1)].ival)==1 && (yysemantic_stack_[(2) - (2)].ival)==1) {
    map<string, basictype *>* a = new map<string, basictype *>;
    vector<basictype *>* b = new vector<basictype *>;
    (yyval.map_vec_basictype) = new pair<map<string, basictype *>*, vector<basictype *>* >(a, b);
  } else
    (yyval.map_vec_basictype) = NULL;
 }
    break;

  case 77:

/* Line 690 of lalr1.cc  */
#line 674 "parser/nssis_new.yy"
    {
  (yyval.map_vec_basictype) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 78:

/* Line 690 of lalr1.cc  */
#line 680 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].ival)==1 && (yysemantic_stack_[(3) - (3)].ival)==1)
    (yyval.map_vec_basictype) = (yysemantic_stack_[(3) - (2)].map_vec_basictype);
  else
    (yyval.map_vec_basictype) = NULL;
 }
    break;

  case 79:

/* Line 690 of lalr1.cc  */
#line 686 "parser/nssis_new.yy"
    {
  (yyval.map_vec_basictype) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 80:

/* Line 690 of lalr1.cc  */
#line 692 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 81:

/* Line 690 of lalr1.cc  */
#line 695 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 82:

/* Line 690 of lalr1.cc  */
#line 699 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 83:

/* Line 690 of lalr1.cc  */
#line 703 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 84:

/* Line 690 of lalr1.cc  */
#line 707 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 85:

/* Line 690 of lalr1.cc  */
#line 710 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 86:

/* Line 690 of lalr1.cc  */
#line 714 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 87:

/* Line 690 of lalr1.cc  */
#line 718 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 88:

/* Line 690 of lalr1.cc  */
#line 723 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].ival)==1 && (yysemantic_stack_[(3) - (3)].ival)==1)
    (yyval._bool_expression) = (yysemantic_stack_[(3) - (2)]._bool_expression);
  else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 89:

/* Line 690 of lalr1.cc  */
#line 729 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL; 
 }
    break;

  case 90:

/* Line 690 of lalr1.cc  */
#line 732 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 91:

/* Line 690 of lalr1.cc  */
#line 737 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].ival)==1 && (yysemantic_stack_[(3) - (3)].ival)==1)
    (yyval._bool_expression) = (yysemantic_stack_[(3) - (2)]._bool_expression);
  else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 92:

/* Line 690 of lalr1.cc  */
#line 743 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL; 
 }
    break;

  case 93:

/* Line 690 of lalr1.cc  */
#line 746 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 94:

/* Line 690 of lalr1.cc  */
#line 751 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = (yysemantic_stack_[(2) - (1)]._bool_expression);
  }
    break;

  case 95:

/* Line 690 of lalr1.cc  */
#line 754 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(2) - (1)]._bool_expression));
  }
    break;

  case 96:

/* Line 690 of lalr1.cc  */
#line 759 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 97:

/* Line 690 of lalr1.cc  */
#line 764 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = (yysemantic_stack_[(2) - (1)]._bool_expression);
  }
    break;

  case 98:

/* Line 690 of lalr1.cc  */
#line 767 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(2) - (1)]._bool_expression));
  }
    break;

  case 99:

/* Line 690 of lalr1.cc  */
#line 772 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 100:

/* Line 690 of lalr1.cc  */
#line 779 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 101:

/* Line 690 of lalr1.cc  */
#line 782 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 102:

/* Line 690 of lalr1.cc  */
#line 786 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 103:

/* Line 690 of lalr1.cc  */
#line 790 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 104:

/* Line 690 of lalr1.cc  */
#line 794 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 105:

/* Line 690 of lalr1.cc  */
#line 797 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 106:

/* Line 690 of lalr1.cc  */
#line 801 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 107:

/* Line 690 of lalr1.cc  */
#line 805 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 108:

/* Line 690 of lalr1.cc  */
#line 809 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].ival)==1 && (yysemantic_stack_[(3) - (3)].ival)==1)
    (yyval.vector_evolution_line) = (yysemantic_stack_[(3) - (2)].vector_evolution_line);
  else
    (yyval.vector_evolution_line) = NULL;
 }
    break;

  case 109:

/* Line 690 of lalr1.cc  */
#line 815 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (1)].ival)==1 && (yysemantic_stack_[(2) - (2)].ival)==1)
    (yyval.vector_evolution_line) = new vector<evolution_line *>;
  else
    (yyval.vector_evolution_line) = NULL;
 }
    break;

  case 110:

/* Line 690 of lalr1.cc  */
#line 821 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(1) - (1)]._evolution_line)!=NULL) {
    (yyval.vector_evolution_line) = new vector<evolution_line *>;
    (yyval.vector_evolution_line)->push_back((yysemantic_stack_[(1) - (1)]._evolution_line));
  } else
    (yyval.vector_evolution_line) = NULL;
 }
    break;

  case 111:

/* Line 690 of lalr1.cc  */
#line 828 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (1)].vector_evolution_line)!=NULL && (yysemantic_stack_[(2) - (2)]._evolution_line)!=NULL) {
    (yysemantic_stack_[(2) - (1)].vector_evolution_line)->push_back((yysemantic_stack_[(2) - (2)]._evolution_line));
    (yyval.vector_evolution_line) = (yysemantic_stack_[(2) - (1)].vector_evolution_line);
  } else
    (yyval.vector_evolution_line) = NULL;
 }
    break;

  case 112:

/* Line 690 of lalr1.cc  */
#line 835 "parser/nssis_new.yy"
    {
  (yyval.vector_evolution_line) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 113:

/* Line 690 of lalr1.cc  */
#line 839 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(4) - (1)].vector_assignment)!=NULL && (yysemantic_stack_[(4) - (3)]._bool_expression)!=NULL) 
    (yyval._evolution_line) = new evolution_line((yysemantic_stack_[(4) - (1)].vector_assignment), (yysemantic_stack_[(4) - (3)]._bool_expression));
  else
    (yyval._evolution_line) = NULL;
 }
    break;

  case 114:

/* Line 690 of lalr1.cc  */
#line 845 "parser/nssis_new.yy"
    {
  (yyval._evolution_line) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 115:

/* Line 690 of lalr1.cc  */
#line 849 "parser/nssis_new.yy"
    {
  (yyval.vector_assignment) = (yysemantic_stack_[(3) - (2)].vector_assignment);
 }
    break;

  case 116:

/* Line 690 of lalr1.cc  */
#line 852 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].vector_assignment)!=NULL && (yysemantic_stack_[(3) - (3)].vector_assignment)!=NULL) {
    (yyval.vector_assignment) = (yysemantic_stack_[(3) - (1)].vector_assignment);
    vector<assignment*>::iterator i;
    for(i=(yysemantic_stack_[(3) - (3)].vector_assignment)->begin(); i != (yysemantic_stack_[(3) - (3)].vector_assignment)->end(); i++)
      (yyval.vector_assignment)->push_back(*i);
  } else
    (yyval.vector_assignment) = NULL;
 }
    break;

  case 117:

/* Line 690 of lalr1.cc  */
#line 861 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].sval)!=NULL && (yysemantic_stack_[(3) - (3)]._expression)!=NULL) {
    assignment *a;
    int i = search_string_table((yysemantic_stack_[(3) - (1)].sval));
    if(i>=0) {
      a = new assignment((*string_table)[i], (yysemantic_stack_[(3) - (3)]._expression));
      free((yysemantic_stack_[(3) - (1)].sval));
    } else {
      a = new assignment((yysemantic_stack_[(3) - (1)].sval), (yysemantic_stack_[(3) - (3)]._expression));
      string_table->push_back((yysemantic_stack_[(3) - (1)].sval));
    }
    (yyval.vector_assignment) = new vector<assignment*>;
    (yyval.vector_assignment)->push_back(a);
  } else
    (yyval.vector_assignment) = NULL;
 }
    break;

  case 118:

/* Line 690 of lalr1.cc  */
#line 877 "parser/nssis_new.yy"
    {
  (yyval.vector_assignment) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 119:

/* Line 690 of lalr1.cc  */
#line 882 "parser/nssis_new.yy"
    {
  (yyval.vector_assignment) = (yysemantic_stack_[(3) - (2)].vector_assignment);
 }
    break;

  case 120:

/* Line 690 of lalr1.cc  */
#line 885 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].vector_assignment)!=NULL && (yysemantic_stack_[(3) - (3)].vector_assignment)!=NULL) {
    (yyval.vector_assignment) = (yysemantic_stack_[(3) - (1)].vector_assignment);
    vector<assignment*>::iterator i;
    for(i=(yysemantic_stack_[(3) - (3)].vector_assignment)->begin(); i != (yysemantic_stack_[(3) - (3)].vector_assignment)->end(); i++)
      (yyval.vector_assignment)->push_back(*i);
  } else
    (yyval.vector_assignment) = NULL;
 }
    break;

  case 121:

/* Line 690 of lalr1.cc  */
#line 894 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].sval)!=NULL && (yysemantic_stack_[(3) - (3)]._expression)!=NULL) {
    assignment *a;
    int i = search_string_table((yysemantic_stack_[(3) - (1)].sval));
    if(i>=0) {
      a = new assignment((*string_table)[i], (yysemantic_stack_[(3) - (3)]._expression));
      free((yysemantic_stack_[(3) - (1)].sval));
    } else {
      a = new assignment((yysemantic_stack_[(3) - (1)].sval), (yysemantic_stack_[(3) - (3)]._expression));
      string_table->push_back((yysemantic_stack_[(3) - (1)].sval));
    }
    (yyval.vector_assignment) = new vector<assignment*>;
    (yyval.vector_assignment)->push_back(a);
  } else
    (yyval.vector_assignment) = NULL;
 }
    break;

  case 122:

/* Line 690 of lalr1.cc  */
#line 910 "parser/nssis_new.yy"
    {
  (yyval.vector_assignment) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 123:

/* Line 690 of lalr1.cc  */
#line 915 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(1) - (1)]._basic_agent)!=NULL) {
    (*is_agents)[(yysemantic_stack_[(1) - (1)]._basic_agent)->get_name()] = (yysemantic_stack_[(1) - (1)]._basic_agent);
    agents->push_back((yysemantic_stack_[(1) - (1)]._basic_agent));
  } 
 }
    break;

  case 124:

/* Line 690 of lalr1.cc  */
#line 921 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)]._basic_agent)!=NULL) {
    if(is_agents->find((yysemantic_stack_[(2) - (2)]._basic_agent)->get_name()) != is_agents->end()) {
			if (options["quiet"] == 0)
				cout << "warning: agent " << (yysemantic_stack_[(2) - (2)]._basic_agent)->get_name() << " already exists." << endl;
    } else
      agents->push_back((yysemantic_stack_[(2) - (2)]._basic_agent));
    (*is_agents)[(yysemantic_stack_[(2) - (2)]._basic_agent)->get_name()] = (yysemantic_stack_[(2) - (2)]._basic_agent);
  }
 }
    break;

  case 125:

/* Line 690 of lalr1.cc  */
#line 931 "parser/nssis_new.yy"
    {
  driver.syntax_error = true;
  }
    break;

  case 126:

/* Line 690 of lalr1.cc  */
#line 935 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 127:

/* Line 690 of lalr1.cc  */
#line 938 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 128:

/* Line 690 of lalr1.cc  */
#line 942 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 129:

/* Line 690 of lalr1.cc  */
#line 945 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 130:

/* Line 690 of lalr1.cc  */
#line 949 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 131:

/* Line 690 of lalr1.cc  */
#line 953 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 132:

/* Line 690 of lalr1.cc  */
#line 958 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(8) - (1)].ival)==1 && (yysemantic_stack_[(8) - (2)].sval)!=NULL && (yysemantic_stack_[(8) - (3)].map_vec_basictype)!=NULL && 
     (yysemantic_stack_[(8) - (5)].set_string)!=NULL && (yysemantic_stack_[(8) - (6)].vector_protocol_line)!=NULL && (yysemantic_stack_[(8) - (7)].vector_evolution_line)!=NULL && (yysemantic_stack_[(8) - (8)].ival)==1) {// redstates is NULL if no red state at all
    int i = search_string_table((yysemantic_stack_[(8) - (2)].sval));
    if(i>=0) {
      (yyval._basic_agent) = new basic_agent((*string_table)[i], NULL, NULL, NULL, (yysemantic_stack_[(8) - (3)].map_vec_basictype)->first, (yysemantic_stack_[(8) - (3)].map_vec_basictype)->second, (yysemantic_stack_[(8) - (4)]._bool_expression), (yysemantic_stack_[(8) - (5)].set_string), (yysemantic_stack_[(8) - (6)].vector_protocol_line), (yysemantic_stack_[(8) - (7)].vector_evolution_line));
      free((yysemantic_stack_[(8) - (2)].sval));
    } else {
      (yyval._basic_agent) = new basic_agent((yysemantic_stack_[(8) - (2)].sval), NULL, NULL, NULL, (yysemantic_stack_[(8) - (3)].map_vec_basictype)->first, (yysemantic_stack_[(8) - (3)].map_vec_basictype)->second, (yysemantic_stack_[(8) - (4)]._bool_expression), (yysemantic_stack_[(8) - (5)].set_string), (yysemantic_stack_[(8) - (6)].vector_protocol_line), (yysemantic_stack_[(8) - (7)].vector_evolution_line));
      string_table->push_back((yysemantic_stack_[(8) - (2)].sval));
    }
  } else
    (yyval._basic_agent) = NULL;
 }
    break;

  case 133:

/* Line 690 of lalr1.cc  */
#line 972 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(7) - (1)].ival)==1 && (yysemantic_stack_[(7) - (2)].sval)!=NULL && (yysemantic_stack_[(7) - (3)].map_vec_basictype)!=NULL && 
     (yysemantic_stack_[(7) - (4)].set_string)!=NULL && (yysemantic_stack_[(7) - (5)].vector_protocol_line)!=NULL && (yysemantic_stack_[(7) - (6)].vector_evolution_line)!=NULL && (yysemantic_stack_[(7) - (7)].ival)==1) {// redstates is NULL if no red state at all
    int i = search_string_table((yysemantic_stack_[(7) - (2)].sval));
    if(i>=0) {
      (yyval._basic_agent) = new basic_agent((*string_table)[i], NULL, NULL, NULL, (yysemantic_stack_[(7) - (3)].map_vec_basictype)->first, (yysemantic_stack_[(7) - (3)].map_vec_basictype)->second, NULL, (yysemantic_stack_[(7) - (4)].set_string), (yysemantic_stack_[(7) - (5)].vector_protocol_line), (yysemantic_stack_[(7) - (6)].vector_evolution_line));
      free((yysemantic_stack_[(7) - (2)].sval));
    } else {
      (yyval._basic_agent) = new basic_agent((yysemantic_stack_[(7) - (2)].sval), NULL, NULL, NULL, (yysemantic_stack_[(7) - (3)].map_vec_basictype)->first, (yysemantic_stack_[(7) - (3)].map_vec_basictype)->second, NULL, (yysemantic_stack_[(7) - (4)].set_string), (yysemantic_stack_[(7) - (5)].vector_protocol_line), (yysemantic_stack_[(7) - (6)].vector_evolution_line));
      string_table->push_back((yysemantic_stack_[(7) - (2)].sval));
    }
  } else
    (yyval._basic_agent) = NULL;
 }
    break;

  case 134:

/* Line 690 of lalr1.cc  */
#line 986 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(9) - (1)].ival)==1 && (yysemantic_stack_[(9) - (2)].sval)!=NULL && (yysemantic_stack_[(9) - (4)].map_vec_basictype)!=NULL && 
     (yysemantic_stack_[(9) - (6)].set_string)!=NULL && (yysemantic_stack_[(9) - (7)].vector_protocol_line)!=NULL && (yysemantic_stack_[(9) - (8)].vector_evolution_line)!=NULL && (yysemantic_stack_[(9) - (9)].ival)==1) {// redstates is NULL if no red state at all
    int i = search_string_table((yysemantic_stack_[(9) - (2)].sval));
    if(i>=0) {
      (yyval._basic_agent) = new basic_agent((*string_table)[i], (yysemantic_stack_[(9) - (3)].map_string_variable), NULL, NULL, (yysemantic_stack_[(9) - (4)].map_vec_basictype)->first, (yysemantic_stack_[(9) - (4)].map_vec_basictype)->second, (yysemantic_stack_[(9) - (5)]._bool_expression), (yysemantic_stack_[(9) - (6)].set_string), (yysemantic_stack_[(9) - (7)].vector_protocol_line), (yysemantic_stack_[(9) - (8)].vector_evolution_line));
      free((yysemantic_stack_[(9) - (2)].sval));
    } else {
      (yyval._basic_agent) = new basic_agent((yysemantic_stack_[(9) - (2)].sval), (yysemantic_stack_[(9) - (3)].map_string_variable), NULL, NULL, (yysemantic_stack_[(9) - (4)].map_vec_basictype)->first, (yysemantic_stack_[(9) - (4)].map_vec_basictype)->second, (yysemantic_stack_[(9) - (5)]._bool_expression), (yysemantic_stack_[(9) - (6)].set_string), (yysemantic_stack_[(9) - (7)].vector_protocol_line), (yysemantic_stack_[(9) - (8)].vector_evolution_line));
      string_table->push_back((yysemantic_stack_[(9) - (2)].sval));
    }
  } else
    (yyval._basic_agent) = NULL;
 }
    break;

  case 135:

/* Line 690 of lalr1.cc  */
#line 1000 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(8) - (1)].ival)==1 && (yysemantic_stack_[(8) - (2)].sval)!=NULL && 
     (yysemantic_stack_[(8) - (4)].map_vec_basictype)!=NULL && (yysemantic_stack_[(8) - (5)].set_string)!=NULL && (yysemantic_stack_[(8) - (6)].vector_protocol_line)!=NULL && (yysemantic_stack_[(8) - (7)].vector_evolution_line)!=NULL && (yysemantic_stack_[(8) - (8)].ival)==1) {// redstates is NULL if no red state at all
    int i = search_string_table((yysemantic_stack_[(8) - (2)].sval));
    if(i>=0) {
      (yyval._basic_agent) = new basic_agent((*string_table)[i], (yysemantic_stack_[(8) - (3)].map_string_variable), NULL, NULL, (yysemantic_stack_[(8) - (4)].map_vec_basictype)->first, (yysemantic_stack_[(8) - (4)].map_vec_basictype)->second, NULL, (yysemantic_stack_[(8) - (5)].set_string), (yysemantic_stack_[(8) - (6)].vector_protocol_line), (yysemantic_stack_[(8) - (7)].vector_evolution_line));
      free((yysemantic_stack_[(8) - (2)].sval));
    } else {
      (yyval._basic_agent) = new basic_agent((yysemantic_stack_[(8) - (2)].sval), (yysemantic_stack_[(8) - (3)].map_string_variable), NULL, NULL, (yysemantic_stack_[(8) - (4)].map_vec_basictype)->first, (yysemantic_stack_[(8) - (4)].map_vec_basictype)->second, NULL, (yysemantic_stack_[(8) - (5)].set_string), (yysemantic_stack_[(8) - (6)].vector_protocol_line), (yysemantic_stack_[(8) - (7)].vector_evolution_line));
      string_table->push_back((yysemantic_stack_[(8) - (2)].sval));
    }
  } else
    (yyval._basic_agent) = NULL;
 }
    break;

  case 136:

/* Line 690 of lalr1.cc  */
#line 1014 "parser/nssis_new.yy"
    {
  (yyval._basic_agent) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 137:

/* Line 690 of lalr1.cc  */
#line 1020 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 138:

/* Line 690 of lalr1.cc  */
#line 1023 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 139:

/* Line 690 of lalr1.cc  */
#line 1027 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 140:

/* Line 690 of lalr1.cc  */
#line 1031 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 141:

/* Line 690 of lalr1.cc  */
#line 1035 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 142:

/* Line 690 of lalr1.cc  */
#line 1039 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 143:

/* Line 690 of lalr1.cc  */
#line 1043 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 144:

/* Line 690 of lalr1.cc  */
#line 1047 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 145:

/* Line 690 of lalr1.cc  */
#line 1051 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 146:

/* Line 690 of lalr1.cc  */
#line 1054 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 147:

/* Line 690 of lalr1.cc  */
#line 1058 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 148:

/* Line 690 of lalr1.cc  */
#line 1062 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 149:

/* Line 690 of lalr1.cc  */
#line 1066 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].ival)==1 && (yysemantic_stack_[(3) - (3)].ival)==1)
    (yyval.map_string_variable) = (yysemantic_stack_[(3) - (2)].map_string_variable);
  else
    (yyval.map_string_variable) = NULL;
 }
    break;

  case 150:

/* Line 690 of lalr1.cc  */
#line 1072 "parser/nssis_new.yy"
    {
  (yyval.map_string_variable) = NULL;
 }
    break;

  case 151:

/* Line 690 of lalr1.cc  */
#line 1075 "parser/nssis_new.yy"
    {
  (yyval.map_string_variable) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 152:

/* Line 690 of lalr1.cc  */
#line 1079 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(1) - (1)].sval)!=NULL) {
    (yyval.map_string_variable) = new map<string, variable *>;
    if((yyval.map_string_variable)->find(*(yysemantic_stack_[(1) - (1)].sval)) != (yyval.map_string_variable)->end() && options["quiet"] == 0)
      cout << "warning: local observable variable " << *(yysemantic_stack_[(1) - (1)].sval) << " has already been defined." << endl;
    int i = search_string_table((yysemantic_stack_[(1) - (1)].sval));
    if(i>=0) {
      (*(yyval.map_string_variable))[*(yysemantic_stack_[(1) - (1)].sval)] = new variable((*string_table)[0], (*string_table)[i]);
      free((yysemantic_stack_[(1) - (1)].sval));
    } else {
      (*(yyval.map_string_variable))[*(yysemantic_stack_[(1) - (1)].sval)] = new variable((*string_table)[0], (yysemantic_stack_[(1) - (1)].sval));
      string_table->push_back((yysemantic_stack_[(1) - (1)].sval));
    }
  } else
    (yyval.map_string_variable) = NULL;
 }
    break;

  case 153:

/* Line 690 of lalr1.cc  */
#line 1095 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].map_string_variable)!=NULL && (yysemantic_stack_[(3) - (3)].sval)!=NULL) {
    if((yysemantic_stack_[(3) - (1)].map_string_variable)->find(*(yysemantic_stack_[(3) - (3)].sval)) != (yyval.map_string_variable)->end() && options["quiet"] == 0)
      cout << "warning: local observable variable " << *(yysemantic_stack_[(3) - (3)].sval) << " has already been defined." << endl;
    int i = search_string_table((yysemantic_stack_[(3) - (3)].sval));
    if(i>=0) {
      (*(yysemantic_stack_[(3) - (1)].map_string_variable))[*(yysemantic_stack_[(3) - (3)].sval)] = new variable((*string_table)[0], (*string_table)[i]);
      free((yysemantic_stack_[(3) - (3)].sval));
    } else {
      (*(yysemantic_stack_[(3) - (1)].map_string_variable))[*(yysemantic_stack_[(3) - (3)].sval)] = new variable((*string_table)[0], (yysemantic_stack_[(3) - (3)].sval));
      string_table->push_back((yysemantic_stack_[(3) - (3)].sval));
    }
    (yyval.map_string_variable) = (yysemantic_stack_[(3) - (1)].map_string_variable);
  } else
    (yyval.map_string_variable) = NULL;
 }
    break;

  case 154:

/* Line 690 of lalr1.cc  */
#line 1111 "parser/nssis_new.yy"
    {
  (yyval.map_string_variable) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)].map_string_variable));
  USE((yysemantic_stack_[(3) - (3)].sval));
 }
    break;

  case 155:

/* Line 690 of lalr1.cc  */
#line 1117 "parser/nssis_new.yy"
    {
  (yyval.map_string_variable) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 156:

/* Line 690 of lalr1.cc  */
#line 1124 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 157:

/* Line 690 of lalr1.cc  */
#line 1127 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 158:

/* Line 690 of lalr1.cc  */
#line 1131 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 159:

/* Line 690 of lalr1.cc  */
#line 1135 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 160:

/* Line 690 of lalr1.cc  */
#line 1139 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 161:

/* Line 690 of lalr1.cc  */
#line 1143 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 162:

/* Line 690 of lalr1.cc  */
#line 1147 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 163:

/* Line 690 of lalr1.cc  */
#line 1151 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 164:

/* Line 690 of lalr1.cc  */
#line 1155 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 165:

/* Line 690 of lalr1.cc  */
#line 1158 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 166:

/* Line 690 of lalr1.cc  */
#line 1162 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 167:

/* Line 690 of lalr1.cc  */
#line 1166 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 168:

/* Line 690 of lalr1.cc  */
#line 1170 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].ival)==1 && (yysemantic_stack_[(3) - (3)].ival)==1)
    (yyval.set_string) = (yysemantic_stack_[(3) - (2)].set_string);
  else
    (yyval.set_string) = NULL;
 }
    break;

  case 169:

/* Line 690 of lalr1.cc  */
#line 1176 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (1)].ival)==1 && (yysemantic_stack_[(2) - (2)].ival)==1)
    (yyval.set_string) = new set<string>;
  else
    (yyval.set_string) = NULL;
 }
    break;

  case 170:

/* Line 690 of lalr1.cc  */
#line 1182 "parser/nssis_new.yy"
    {
  (yyval.set_string) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 171:

/* Line 690 of lalr1.cc  */
#line 1188 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].ival)==1 && (yysemantic_stack_[(3) - (3)].ival)==1) 
    (yyval.set_string) = (yysemantic_stack_[(3) - (2)].set_string);
  else
    (yyval.set_string) = NULL;
 }
    break;

  case 172:

/* Line 690 of lalr1.cc  */
#line 1194 "parser/nssis_new.yy"
    {
  (yyval.set_string) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 173:

/* Line 690 of lalr1.cc  */
#line 1198 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(1) - (1)].sval)!=NULL) {
    (yyval.set_string) = new set<string>;
    (yyval.set_string)->insert(*(yysemantic_stack_[(1) - (1)].sval));
    free ((yysemantic_stack_[(1) - (1)].sval));
  } else
    (yyval.set_string) = NULL;
 }
    break;

  case 174:

/* Line 690 of lalr1.cc  */
#line 1206 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].set_string)!=NULL && (yysemantic_stack_[(3) - (3)].sval)!=NULL) {
    pair<set<string>::iterator, bool> ret = (yysemantic_stack_[(3) - (1)].set_string)->insert(*(yysemantic_stack_[(3) - (3)].sval));
    if(!ret.second && options["quiet"] == 0)
      cout << "warning: action " << *(yysemantic_stack_[(3) - (3)].sval) << " has been defined." << endl;
    (yyval.set_string) = (yysemantic_stack_[(3) - (1)].set_string);
    free ((yysemantic_stack_[(3) - (3)].sval));
  } else
    (yyval.set_string) = NULL;
 }
    break;

  case 175:

/* Line 690 of lalr1.cc  */
#line 1216 "parser/nssis_new.yy"
    {
  (yyval.set_string) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)].set_string));
  USE((yysemantic_stack_[(3) - (3)].sval));
 }
    break;

  case 176:

/* Line 690 of lalr1.cc  */
#line 1222 "parser/nssis_new.yy"
    {
  (yyval.set_string) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 177:

/* Line 690 of lalr1.cc  */
#line 1229 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 178:

/* Line 690 of lalr1.cc  */
#line 1232 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 179:

/* Line 690 of lalr1.cc  */
#line 1236 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 180:

/* Line 690 of lalr1.cc  */
#line 1240 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 181:

/* Line 690 of lalr1.cc  */
#line 1244 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 182:

/* Line 690 of lalr1.cc  */
#line 1247 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 183:

/* Line 690 of lalr1.cc  */
#line 1251 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 184:

/* Line 690 of lalr1.cc  */
#line 1255 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 185:

/* Line 690 of lalr1.cc  */
#line 1260 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].ival)==1 && (yysemantic_stack_[(3) - (3)].ival)==1) 
    (yyval.vector_protocol_line) = (yysemantic_stack_[(3) - (2)].vector_protocol_line);
  else
    (yyval.vector_protocol_line) = NULL;
 }
    break;

  case 186:

/* Line 690 of lalr1.cc  */
#line 1266 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(4) - (1)].ival)==1 && (yysemantic_stack_[(4) - (4)].ival)==1) {
    (yyval.vector_protocol_line) = (yysemantic_stack_[(4) - (2)].vector_protocol_line);
    (yyval.vector_protocol_line)->push_back((yysemantic_stack_[(4) - (3)]._protocol_line));
  }
  else
    (yyval.vector_protocol_line) = NULL;
 }
    break;

  case 187:

/* Line 690 of lalr1.cc  */
#line 1274 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].ival)==1 && (yysemantic_stack_[(3) - (3)].ival)==1) {
    (yyval.vector_protocol_line) = new vector<protocol_line*>;
    (yyval.vector_protocol_line)->push_back((yysemantic_stack_[(3) - (2)]._protocol_line));;
  }
  else
    (yyval.vector_protocol_line) = NULL;
 }
    break;

  case 188:

/* Line 690 of lalr1.cc  */
#line 1282 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (1)].ival)==1 && (yysemantic_stack_[(2) - (2)].ival)==1) 
    (yyval.vector_protocol_line) = new vector<protocol_line*>;
  else
    (yyval.vector_protocol_line) = NULL;
 }
    break;

  case 189:

/* Line 690 of lalr1.cc  */
#line 1288 "parser/nssis_new.yy"
    {
  (yyval.vector_protocol_line) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 190:

/* Line 690 of lalr1.cc  */
#line 1294 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].ival)==1 && (yysemantic_stack_[(3) - (3)].ival)==1) 
    (yyval.vector_protocol_line) = (yysemantic_stack_[(3) - (2)].vector_protocol_line);
  else
    (yyval.vector_protocol_line) = NULL;
 }
    break;

  case 191:

/* Line 690 of lalr1.cc  */
#line 1300 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(4) - (1)].ival)==1 && (yysemantic_stack_[(4) - (4)].ival)==1) {
    (yyval.vector_protocol_line) = (yysemantic_stack_[(4) - (2)].vector_protocol_line);
    (yyval.vector_protocol_line)->push_back((yysemantic_stack_[(4) - (3)]._protocol_line));
  }
  else
    (yyval.vector_protocol_line) = NULL;
 }
    break;

  case 192:

/* Line 690 of lalr1.cc  */
#line 1308 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].ival)==1 && (yysemantic_stack_[(3) - (3)].ival)==1) {
    (yyval.vector_protocol_line) = new vector<protocol_line*>;
    (yyval.vector_protocol_line)->push_back((yysemantic_stack_[(3) - (2)]._protocol_line));;
  }
  else
    (yyval.vector_protocol_line) = NULL;
 }
    break;

  case 193:

/* Line 690 of lalr1.cc  */
#line 1316 "parser/nssis_new.yy"
    {
  (yyval.vector_protocol_line) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 194:

/* Line 690 of lalr1.cc  */
#line 1321 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(1) - (1)]._protocol_line)!=NULL) {
    (yyval.vector_protocol_line) = new vector<protocol_line*>;
    (yyval.vector_protocol_line)->push_back((yysemantic_stack_[(1) - (1)]._protocol_line));
  } else
    (yyval.vector_protocol_line) = NULL;
 }
    break;

  case 195:

/* Line 690 of lalr1.cc  */
#line 1328 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (1)].vector_protocol_line)!=NULL && (yysemantic_stack_[(2) - (2)]._protocol_line)!=NULL) {
    (yysemantic_stack_[(2) - (1)].vector_protocol_line)->push_back((yysemantic_stack_[(2) - (2)]._protocol_line));
    (yyval.vector_protocol_line) = (yysemantic_stack_[(2) - (1)].vector_protocol_line);
  } else
    (yyval.vector_protocol_line) = NULL;
 }
    break;

  case 196:

/* Line 690 of lalr1.cc  */
#line 1335 "parser/nssis_new.yy"
    {
  (yyval.vector_protocol_line) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 197:

/* Line 690 of lalr1.cc  */
#line 1340 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(1) - (1)]._protocol_line)!=NULL) {
    (yyval.vector_protocol_line) = new vector<protocol_line*>;
    (yyval.vector_protocol_line)->push_back((yysemantic_stack_[(1) - (1)]._protocol_line));
  } else
    (yyval.vector_protocol_line) = NULL;
 }
    break;

  case 198:

/* Line 690 of lalr1.cc  */
#line 1347 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (1)].vector_protocol_line)!=NULL && (yysemantic_stack_[(2) - (2)]._protocol_line)!=NULL) {
    (yysemantic_stack_[(2) - (1)].vector_protocol_line)->push_back((yysemantic_stack_[(2) - (2)]._protocol_line));
    (yyval.vector_protocol_line) = (yysemantic_stack_[(2) - (1)].vector_protocol_line);
  } else
    (yyval.vector_protocol_line) = NULL;
 }
    break;

  case 199:

/* Line 690 of lalr1.cc  */
#line 1354 "parser/nssis_new.yy"
    {
  (yyval.vector_protocol_line) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 200:

/* Line 690 of lalr1.cc  */
#line 1359 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 201:

/* Line 690 of lalr1.cc  */
#line 1362 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 202:

/* Line 690 of lalr1.cc  */
#line 1366 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 203:

/* Line 690 of lalr1.cc  */
#line 1370 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 204:

/* Line 690 of lalr1.cc  */
#line 1374 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 205:

/* Line 690 of lalr1.cc  */
#line 1377 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 206:

/* Line 690 of lalr1.cc  */
#line 1381 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 207:

/* Line 690 of lalr1.cc  */
#line 1385 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 208:

/* Line 690 of lalr1.cc  */
#line 1389 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(4) - (1)]._bool_expression)!=NULL && (yysemantic_stack_[(4) - (2)].ival)==1 && (yysemantic_stack_[(4) - (3)].set_string)!=NULL && (yysemantic_stack_[(4) - (4)].ival)==1) 
    (yyval._protocol_line) = new protocol_line((yysemantic_stack_[(4) - (1)]._bool_expression), (yysemantic_stack_[(4) - (3)].set_string));
  else
    (yyval._protocol_line) = NULL;
 }
    break;

  case 209:

/* Line 690 of lalr1.cc  */
#line 1395 "parser/nssis_new.yy"
    {
  (yyval._protocol_line) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 210:

/* Line 690 of lalr1.cc  */
#line 1400 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(4) - (1)]._bool_expression)!=NULL && (yysemantic_stack_[(4) - (2)].ival)==1 && (yysemantic_stack_[(4) - (3)].set_string)!=NULL && (yysemantic_stack_[(4) - (4)].ival)==1) 
    (yyval._protocol_line) = new protocol_line((yysemantic_stack_[(4) - (1)]._bool_expression), (yysemantic_stack_[(4) - (3)].set_string));
  else
    (yyval._protocol_line) = NULL;
 }
    break;

  case 211:

/* Line 690 of lalr1.cc  */
#line 1406 "parser/nssis_new.yy"
    {
  (yyval._protocol_line) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 212:

/* Line 690 of lalr1.cc  */
#line 1411 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(4) - (2)].ival)==1 && (yysemantic_stack_[(4) - (3)].set_string)!=NULL && (yysemantic_stack_[(4) - (4)].ival)==1) 
    (yyval._protocol_line) = new protocol_line(new bool_expression(), (yysemantic_stack_[(4) - (3)].set_string));
  else
    (yyval._protocol_line) = NULL;
 }
    break;

  case 213:

/* Line 690 of lalr1.cc  */
#line 1417 "parser/nssis_new.yy"
    {
  (yyval._protocol_line) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(4) - (3)].set_string));
 }
    break;

  case 214:

/* Line 690 of lalr1.cc  */
#line 1423 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(1) - (1)].sval)!=NULL) {
    (yyval.set_string) = new set<string>;
    (yyval.set_string)->insert(*(yysemantic_stack_[(1) - (1)].sval));
    free ((yysemantic_stack_[(1) - (1)].sval));
  } else
    (yyval.set_string) = NULL;
 }
    break;

  case 215:

/* Line 690 of lalr1.cc  */
#line 1431 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].set_string)!=NULL && (yysemantic_stack_[(3) - (3)].sval)!=NULL) {
    pair<set<string>::iterator, bool> ret = (yysemantic_stack_[(3) - (1)].set_string)->insert(*(yysemantic_stack_[(3) - (3)].sval));
    if(!ret.second && options["quiet"] == 0)
      cout << "warning: action " << *(yysemantic_stack_[(3) - (3)].sval) << " is repeated." << endl;
    (yyval.set_string) = (yysemantic_stack_[(3) - (1)].set_string);
    free ((yysemantic_stack_[(3) - (3)].sval));
  } else
    (yyval.set_string) = NULL;
 }
    break;

  case 216:

/* Line 690 of lalr1.cc  */
#line 1441 "parser/nssis_new.yy"
    {
  (yyval.set_string) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)].set_string));
  USE((yysemantic_stack_[(3) - (3)].sval));
 }
    break;

  case 217:

/* Line 690 of lalr1.cc  */
#line 1447 "parser/nssis_new.yy"
    {
  (yyval.set_string) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 218:

/* Line 690 of lalr1.cc  */
#line 1454 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].ival)==1 && (yysemantic_stack_[(3) - (3)].ival)==1)
    (yyval.vector_evolution_line) = (yysemantic_stack_[(3) - (2)].vector_evolution_line);
  else
    (yyval.vector_evolution_line) = NULL;
}
    break;

  case 219:

/* Line 690 of lalr1.cc  */
#line 1460 "parser/nssis_new.yy"
    {
  (yyval.vector_evolution_line) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 220:

/* Line 690 of lalr1.cc  */
#line 1464 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(1) - (1)]._evolution_line)!=NULL) {
    (yyval.vector_evolution_line) = new vector<evolution_line*>;
    (yyval.vector_evolution_line)->push_back((yysemantic_stack_[(1) - (1)]._evolution_line));
  } else
    (yyval.vector_evolution_line) = NULL;
 }
    break;

  case 221:

/* Line 690 of lalr1.cc  */
#line 1471 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (1)].vector_evolution_line)!=NULL && (yysemantic_stack_[(2) - (2)]._evolution_line)!=NULL) {
    (yysemantic_stack_[(2) - (1)].vector_evolution_line)->push_back((yysemantic_stack_[(2) - (2)]._evolution_line));
    (yyval.vector_evolution_line) = (yysemantic_stack_[(2) - (1)].vector_evolution_line);
  } else
    (yyval.vector_evolution_line) = NULL;
 }
    break;

  case 222:

/* Line 690 of lalr1.cc  */
#line 1478 "parser/nssis_new.yy"
    {
  (yyval.vector_evolution_line) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 223:

/* Line 690 of lalr1.cc  */
#line 1483 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(4) - (1)].vector_assignment)!=NULL)
    (yyval._evolution_line) = new evolution_line((yysemantic_stack_[(4) - (1)].vector_assignment), (yysemantic_stack_[(4) - (3)]._bool_expression));
  else
    (yyval._evolution_line) = NULL;
 }
    break;

  case 224:

/* Line 690 of lalr1.cc  */
#line 1489 "parser/nssis_new.yy"
    {
  (yyval._evolution_line) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(4) - (1)].vector_assignment));
  USE((yysemantic_stack_[(4) - (3)]._bool_expression));
 }
    break;

  case 225:

/* Line 690 of lalr1.cc  */
#line 1495 "parser/nssis_new.yy"
    {
  (yyval._evolution_line) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(4) - (1)].vector_assignment));
  USE((yysemantic_stack_[(4) - (3)]._bool_expression));
 }
    break;

  case 226:

/* Line 690 of lalr1.cc  */
#line 1501 "parser/nssis_new.yy"
    {
  (yyval._evolution_line) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(4) - (1)].vector_assignment));
  USE((yysemantic_stack_[(4) - (3)]._bool_expression));
 }
    break;

  case 227:

/* Line 690 of lalr1.cc  */
#line 1507 "parser/nssis_new.yy"
    {
  (yyval._evolution_line) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 228:

/* Line 690 of lalr1.cc  */
#line 1512 "parser/nssis_new.yy"
    { 
  (yyval._bool_expression) = (yysemantic_stack_[(3) - (2)]._bool_expression); 
 }
    break;

  case 229:

/* Line 690 of lalr1.cc  */
#line 1515 "parser/nssis_new.yy"
    { 
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._bool_expression));
 }
    break;

  case 230:

/* Line 690 of lalr1.cc  */
#line 1520 "parser/nssis_new.yy"
    { 
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._bool_expression));
 }
    break;

  case 231:

/* Line 690 of lalr1.cc  */
#line 1525 "parser/nssis_new.yy"
    { 
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._bool_expression));
 }
    break;

  case 232:

/* Line 690 of lalr1.cc  */
#line 1530 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._bool_expression)!=NULL && (yysemantic_stack_[(3) - (3)]._bool_expression)!=NULL)
    (yyval._bool_expression) = new bool_expression(1, (yysemantic_stack_[(3) - (1)]._bool_expression), (yysemantic_stack_[(3) - (3)]._bool_expression));
  else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 233:

/* Line 690 of lalr1.cc  */
#line 1536 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._bool_expression)!=NULL && (yysemantic_stack_[(3) - (3)]._bool_expression)!=NULL)
    (yyval._bool_expression) = new bool_expression(2, (yysemantic_stack_[(3) - (1)]._bool_expression), (yysemantic_stack_[(3) - (3)]._bool_expression));
  else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 234:

/* Line 690 of lalr1.cc  */
#line 1542 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)]._bool_expression));
  USE((yysemantic_stack_[(3) - (3)]._bool_expression));
 }
    break;

  case 235:

/* Line 690 of lalr1.cc  */
#line 1548 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)]._bool_expression)!=NULL)
    (yyval._bool_expression) = new bool_expression(3, (yysemantic_stack_[(2) - (2)]._bool_expression));
  else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 236:

/* Line 690 of lalr1.cc  */
#line 1554 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(2) - (2)]._bool_expression));
 }
    break;

  case 237:

/* Line 690 of lalr1.cc  */
#line 1559 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._expression)!=NULL && (yysemantic_stack_[(3) - (3)]._expression)!=NULL) {
    logic_expression *expr = new logic_expression((yysemantic_stack_[(3) - (2)]._unsigned_char), (yysemantic_stack_[(3) - (1)]._expression), (yysemantic_stack_[(3) - (3)]._expression));
    (yyval._bool_expression) = new bool_expression(0,  expr);
  } else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 238:

/* Line 690 of lalr1.cc  */
#line 1566 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 239:

/* Line 690 of lalr1.cc  */
#line 1571 "parser/nssis_new.yy"
    { 
  (yyval._bool_expression) = (yysemantic_stack_[(3) - (2)]._bool_expression); 
 }
    break;

  case 240:

/* Line 690 of lalr1.cc  */
#line 1574 "parser/nssis_new.yy"
    { 
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._bool_expression));
 }
    break;

  case 241:

/* Line 690 of lalr1.cc  */
#line 1579 "parser/nssis_new.yy"
    { 
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._bool_expression));
 }
    break;

  case 242:

/* Line 690 of lalr1.cc  */
#line 1584 "parser/nssis_new.yy"
    { 
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._bool_expression));
 }
    break;

  case 243:

/* Line 690 of lalr1.cc  */
#line 1589 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._bool_expression)!=NULL && (yysemantic_stack_[(3) - (3)]._bool_expression)!=NULL)
    (yyval._bool_expression) = new bool_expression(1, (yysemantic_stack_[(3) - (1)]._bool_expression), (yysemantic_stack_[(3) - (3)]._bool_expression));
  else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 244:

/* Line 690 of lalr1.cc  */
#line 1595 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._bool_expression)!=NULL && (yysemantic_stack_[(3) - (3)]._bool_expression)!=NULL)
    (yyval._bool_expression) = new bool_expression(2, (yysemantic_stack_[(3) - (1)]._bool_expression), (yysemantic_stack_[(3) - (3)]._bool_expression));
  else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 245:

/* Line 690 of lalr1.cc  */
#line 1601 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)]._bool_expression));
  USE((yysemantic_stack_[(3) - (3)]._bool_expression));
 }
    break;

  case 246:

/* Line 690 of lalr1.cc  */
#line 1607 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)]._bool_expression)!=NULL)
    (yyval._bool_expression) = new bool_expression(3, (yysemantic_stack_[(2) - (2)]._bool_expression));
  else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 247:

/* Line 690 of lalr1.cc  */
#line 1613 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(2) - (2)]._bool_expression));
 }
    break;

  case 248:

/* Line 690 of lalr1.cc  */
#line 1618 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._expression)!=NULL && (yysemantic_stack_[(3) - (3)]._expression)!=NULL) {
    logic_expression *expr = new logic_expression((yysemantic_stack_[(3) - (2)]._unsigned_char), (yysemantic_stack_[(3) - (1)]._expression), (yysemantic_stack_[(3) - (3)]._expression));
    (yyval._bool_expression) = new bool_expression(0,  expr);
  } else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 249:

/* Line 690 of lalr1.cc  */
#line 1625 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
 }
    break;

  case 250:

/* Line 690 of lalr1.cc  */
#line 1630 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._expression)!=NULL && (yysemantic_stack_[(3) - (3)]._expression)!=NULL) {
    (yyval._expression) = new arithmetic_expression(5, (yysemantic_stack_[(3) - (1)]._expression), (yysemantic_stack_[(3) - (3)]._expression));
  } else
    (yyval._expression) = NULL;
 }
    break;

  case 251:

/* Line 690 of lalr1.cc  */
#line 1636 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._expression)!=NULL && (yysemantic_stack_[(3) - (3)]._expression)!=NULL) {
    (yyval._expression) = new arithmetic_expression(6, (yysemantic_stack_[(3) - (1)]._expression), (yysemantic_stack_[(3) - (3)]._expression));
  } else
    (yyval._expression) = NULL;
 }
    break;

  case 252:

/* Line 690 of lalr1.cc  */
#line 1642 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)]._expression));
 }
    break;

  case 253:

/* Line 690 of lalr1.cc  */
#line 1647 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(1) - (1)]._expression);
  }
    break;

  case 254:

/* Line 690 of lalr1.cc  */
#line 1650 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._expression)!=NULL && (yysemantic_stack_[(3) - (3)]._expression)!=NULL) {
    (yyval._expression) = new arithmetic_expression(7, (yysemantic_stack_[(3) - (1)]._expression), (yysemantic_stack_[(3) - (3)]._expression));
  } else
    (yyval._expression) = NULL;
 }
    break;

  case 255:

/* Line 690 of lalr1.cc  */
#line 1656 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._expression)!=NULL && (yysemantic_stack_[(3) - (3)]._expression)!=NULL) {
    (yyval._expression) = new arithmetic_expression(8, (yysemantic_stack_[(3) - (1)]._expression), (yysemantic_stack_[(3) - (3)]._expression));
  } else
    (yyval._expression) = NULL;
 }
    break;

  case 256:

/* Line 690 of lalr1.cc  */
#line 1662 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)]._expression));
 }
    break;

  case 257:

/* Line 690 of lalr1.cc  */
#line 1667 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(1) - (1)]._expression);
  }
    break;

  case 258:

/* Line 690 of lalr1.cc  */
#line 1670 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(3) - (2)]._expression);
  }
    break;

  case 259:

/* Line 690 of lalr1.cc  */
#line 1673 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._expression));
 }
    break;

  case 260:

/* Line 690 of lalr1.cc  */
#line 1678 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._expression));
 }
    break;

  case 261:

/* Line 690 of lalr1.cc  */
#line 1683 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(1) - (1)]._expression);
  }
    break;

  case 262:

/* Line 690 of lalr1.cc  */
#line 1687 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._expression)!=NULL && (yysemantic_stack_[(3) - (3)]._expression)!=NULL) {
    (yyval._expression) = new bit_expression(10, (yysemantic_stack_[(3) - (1)]._expression), (yysemantic_stack_[(3) - (3)]._expression));
  } else
    (yyval._expression) = NULL;
 }
    break;

  case 263:

/* Line 690 of lalr1.cc  */
#line 1693 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._expression)!=NULL && (yysemantic_stack_[(3) - (3)]._expression)!=NULL) {
    (yyval._expression) = new bit_expression(12, (yysemantic_stack_[(3) - (1)]._expression), (yysemantic_stack_[(3) - (3)]._expression));
  } else
    (yyval._expression) = NULL;
 }
    break;

  case 264:

/* Line 690 of lalr1.cc  */
#line 1699 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)]._expression));
 }
    break;

  case 265:

/* Line 690 of lalr1.cc  */
#line 1704 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(1) - (1)]._expression);
  }
    break;

  case 266:

/* Line 690 of lalr1.cc  */
#line 1707 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._expression)!=NULL && (yysemantic_stack_[(3) - (3)]._expression)!=NULL) {
    (yyval._expression) = new bit_expression(9, (yysemantic_stack_[(3) - (1)]._expression), (yysemantic_stack_[(3) - (3)]._expression));
  } else
    (yyval._expression) = NULL;
 }
    break;

  case 267:

/* Line 690 of lalr1.cc  */
#line 1713 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)]._expression));
 }
    break;

  case 268:

/* Line 690 of lalr1.cc  */
#line 1718 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(1) - (1)]._expression);
  }
    break;

  case 269:

/* Line 690 of lalr1.cc  */
#line 1721 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)]._expression)!=NULL) {
    (yyval._expression) = new bit_expression(11, (yysemantic_stack_[(2) - (2)]._expression), NULL);
  } else
    (yyval._expression) = NULL;
 }
    break;

  case 270:

/* Line 690 of lalr1.cc  */
#line 1727 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(2) - (2)]._expression));
 }
    break;

  case 271:

/* Line 690 of lalr1.cc  */
#line 1732 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(1) - (1)]._expression);
  }
    break;

  case 272:

/* Line 690 of lalr1.cc  */
#line 1735 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(3) - (2)]._expression);
  }
    break;

  case 273:

/* Line 690 of lalr1.cc  */
#line 1738 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._expression));
 }
    break;

  case 274:

/* Line 690 of lalr1.cc  */
#line 1743 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._expression));
 }
    break;

  case 275:

/* Line 690 of lalr1.cc  */
#line 1748 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(1) - (1)]._expression);
  }
    break;

  case 276:

/* Line 690 of lalr1.cc  */
#line 1752 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._expression)!=NULL && (yysemantic_stack_[(3) - (3)]._expression)!=NULL) {
    (yyval._expression) = new bit_expression(10, (yysemantic_stack_[(3) - (1)]._expression), (yysemantic_stack_[(3) - (3)]._expression));
  } else
    (yyval._expression) = NULL;
 }
    break;

  case 277:

/* Line 690 of lalr1.cc  */
#line 1758 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._expression)!=NULL && (yysemantic_stack_[(3) - (3)]._expression)!=NULL) {
    (yyval._expression) = new bit_expression(12, (yysemantic_stack_[(3) - (1)]._expression), (yysemantic_stack_[(3) - (3)]._expression));
  } else
    (yyval._expression) = NULL;
 }
    break;

  case 278:

/* Line 690 of lalr1.cc  */
#line 1764 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)]._expression));
 }
    break;

  case 279:

/* Line 690 of lalr1.cc  */
#line 1769 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(1) - (1)]._expression);
  }
    break;

  case 280:

/* Line 690 of lalr1.cc  */
#line 1772 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._expression)!=NULL && (yysemantic_stack_[(3) - (3)]._expression)!=NULL) {
    (yyval._expression) = new bit_expression(9, (yysemantic_stack_[(3) - (1)]._expression), (yysemantic_stack_[(3) - (3)]._expression));
  } else
    (yyval._expression) = NULL;
 }
    break;

  case 281:

/* Line 690 of lalr1.cc  */
#line 1778 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)]._expression));
 }
    break;

  case 282:

/* Line 690 of lalr1.cc  */
#line 1783 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(1) - (1)]._expression);
  }
    break;

  case 283:

/* Line 690 of lalr1.cc  */
#line 1786 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)]._expression)!=NULL) {
    (yyval._expression) = new bit_expression(11, (yysemantic_stack_[(2) - (2)]._expression), NULL);
  } else
    (yyval._expression) = NULL;
 }
    break;

  case 284:

/* Line 690 of lalr1.cc  */
#line 1792 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(2) - (2)]._expression));
 }
    break;

  case 285:

/* Line 690 of lalr1.cc  */
#line 1797 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(1) - (1)]._expression);
  }
    break;

  case 286:

/* Line 690 of lalr1.cc  */
#line 1800 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(3) - (2)]._expression);
  }
    break;

  case 287:

/* Line 690 of lalr1.cc  */
#line 1803 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._expression));
 }
    break;

  case 288:

/* Line 690 of lalr1.cc  */
#line 1808 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._expression));
 }
    break;

  case 289:

/* Line 690 of lalr1.cc  */
#line 1813 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(1) - (1)]._expression);
  }
    break;

  case 290:

/* Line 690 of lalr1.cc  */
#line 1817 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._expression)!=NULL && (yysemantic_stack_[(3) - (3)]._expression)!=NULL) {
    (yyval._expression) = new bit_expression(10, (yysemantic_stack_[(3) - (1)]._expression), (yysemantic_stack_[(3) - (3)]._expression));
  } else
    (yyval._expression) = NULL;
 }
    break;

  case 291:

/* Line 690 of lalr1.cc  */
#line 1823 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._expression)!=NULL && (yysemantic_stack_[(3) - (3)]._expression)!=NULL) {
    (yyval._expression) = new bit_expression(12, (yysemantic_stack_[(3) - (1)]._expression), (yysemantic_stack_[(3) - (3)]._expression));
  } else
    (yyval._expression) = NULL;
 }
    break;

  case 292:

/* Line 690 of lalr1.cc  */
#line 1829 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)]._expression));
 }
    break;

  case 293:

/* Line 690 of lalr1.cc  */
#line 1834 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(1) - (1)]._expression);
  }
    break;

  case 294:

/* Line 690 of lalr1.cc  */
#line 1837 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._expression)!=NULL && (yysemantic_stack_[(3) - (3)]._expression)!=NULL) {
    (yyval._expression) = new bit_expression(9, (yysemantic_stack_[(3) - (1)]._expression), (yysemantic_stack_[(3) - (3)]._expression));
  } else
    (yyval._expression) = NULL;
 }
    break;

  case 295:

/* Line 690 of lalr1.cc  */
#line 1843 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)]._expression));
 }
    break;

  case 296:

/* Line 690 of lalr1.cc  */
#line 1848 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(1) - (1)]._expression);
  }
    break;

  case 297:

/* Line 690 of lalr1.cc  */
#line 1851 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)]._expression)!=NULL) {
    (yyval._expression) = new bit_expression(11, (yysemantic_stack_[(2) - (2)]._expression), NULL);
  } else
    (yyval._expression) = NULL;
 }
    break;

  case 298:

/* Line 690 of lalr1.cc  */
#line 1857 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(2) - (2)]._expression));
 }
    break;

  case 299:

/* Line 690 of lalr1.cc  */
#line 1862 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(1) - (1)]._expression);
  }
    break;

  case 300:

/* Line 690 of lalr1.cc  */
#line 1865 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(3) - (2)]._expression);
  }
    break;

  case 301:

/* Line 690 of lalr1.cc  */
#line 1868 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._expression));
 }
    break;

  case 302:

/* Line 690 of lalr1.cc  */
#line 1873 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._expression));
 }
    break;

  case 303:

/* Line 690 of lalr1.cc  */
#line 1878 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(1) - (1)]._expression);
  }
    break;

  case 304:

/* Line 690 of lalr1.cc  */
#line 1882 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._expression)!=NULL && (yysemantic_stack_[(3) - (3)]._expression)!=NULL) {
    (yyval._expression) = new arithmetic_expression(5, (yysemantic_stack_[(3) - (1)]._expression), (yysemantic_stack_[(3) - (3)]._expression));
  } else
    (yyval._expression) = NULL;
 }
    break;

  case 305:

/* Line 690 of lalr1.cc  */
#line 1888 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._expression)!=NULL && (yysemantic_stack_[(3) - (3)]._expression)!=NULL) {
    (yyval._expression) = new arithmetic_expression(6, (yysemantic_stack_[(3) - (1)]._expression), (yysemantic_stack_[(3) - (3)]._expression));
  } else
    (yyval._expression) = NULL;
 }
    break;

  case 306:

/* Line 690 of lalr1.cc  */
#line 1894 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)]._expression));
 }
    break;

  case 307:

/* Line 690 of lalr1.cc  */
#line 1899 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(1) - (1)]._expression);
  }
    break;

  case 308:

/* Line 690 of lalr1.cc  */
#line 1902 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._expression)!=NULL && (yysemantic_stack_[(3) - (3)]._expression)!=NULL) {
    (yyval._expression) = new arithmetic_expression(7, (yysemantic_stack_[(3) - (1)]._expression), (yysemantic_stack_[(3) - (3)]._expression));
  } else
    (yyval._expression) = NULL;
 }
    break;

  case 309:

/* Line 690 of lalr1.cc  */
#line 1908 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._expression)!=NULL && (yysemantic_stack_[(3) - (3)]._expression)!=NULL) {
    (yyval._expression) = new arithmetic_expression(8, (yysemantic_stack_[(3) - (1)]._expression), (yysemantic_stack_[(3) - (3)]._expression));
  } else
    (yyval._expression) = NULL;
 }
    break;

  case 310:

/* Line 690 of lalr1.cc  */
#line 1914 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)]._expression));
 }
    break;

  case 311:

/* Line 690 of lalr1.cc  */
#line 1919 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(1) - (1)]._expression);
  }
    break;

  case 312:

/* Line 690 of lalr1.cc  */
#line 1922 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(3) - (2)]._expression);
  }
    break;

  case 313:

/* Line 690 of lalr1.cc  */
#line 1925 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._expression));
 }
    break;

  case 314:

/* Line 690 of lalr1.cc  */
#line 1930 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._expression));
 }
    break;

  case 315:

/* Line 690 of lalr1.cc  */
#line 1935 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(1) - (1)]._expression);
  }
    break;

  case 316:

/* Line 690 of lalr1.cc  */
#line 1938 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._expression)!=NULL && (yysemantic_stack_[(3) - (3)]._expression)!=NULL) {
    (yyval._expression) = new arithmetic_expression(5, (yysemantic_stack_[(3) - (1)]._expression), (yysemantic_stack_[(3) - (3)]._expression));
  } else
    (yyval._expression) = NULL;
 }
    break;

  case 317:

/* Line 690 of lalr1.cc  */
#line 1944 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._expression)!=NULL && (yysemantic_stack_[(3) - (3)]._expression)!=NULL) {
    (yyval._expression) = new arithmetic_expression(6, (yysemantic_stack_[(3) - (1)]._expression), (yysemantic_stack_[(3) - (3)]._expression));
  } else
    (yyval._expression) = NULL;
 }
    break;

  case 318:

/* Line 690 of lalr1.cc  */
#line 1950 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)]._expression));
 }
    break;

  case 319:

/* Line 690 of lalr1.cc  */
#line 1955 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(1) - (1)]._expression);
  }
    break;

  case 320:

/* Line 690 of lalr1.cc  */
#line 1958 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._expression)!=NULL && (yysemantic_stack_[(3) - (3)]._expression)!=NULL) {
    (yyval._expression) = new arithmetic_expression(7, (yysemantic_stack_[(3) - (1)]._expression), (yysemantic_stack_[(3) - (3)]._expression));
  } else
    (yyval._expression) = NULL;
 }
    break;

  case 321:

/* Line 690 of lalr1.cc  */
#line 1964 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._expression)!=NULL && (yysemantic_stack_[(3) - (3)]._expression)!=NULL) {
    (yyval._expression) = new arithmetic_expression(8, (yysemantic_stack_[(3) - (1)]._expression), (yysemantic_stack_[(3) - (3)]._expression));
  } else
    (yyval._expression) = NULL;
 }
    break;

  case 322:

/* Line 690 of lalr1.cc  */
#line 1970 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)]._expression));
 }
    break;

  case 323:

/* Line 690 of lalr1.cc  */
#line 1975 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(1) - (1)]._expression);
  }
    break;

  case 324:

/* Line 690 of lalr1.cc  */
#line 1978 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(3) - (2)]._expression);
  }
    break;

  case 325:

/* Line 690 of lalr1.cc  */
#line 1981 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._expression));
 }
    break;

  case 326:

/* Line 690 of lalr1.cc  */
#line 1986 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._expression));
 }
    break;

  case 327:

/* Line 690 of lalr1.cc  */
#line 1991 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(1) - (1)]._expression);
  }
    break;

  case 328:

/* Line 690 of lalr1.cc  */
#line 1997 "parser/nssis_new.yy"
    { 
  (yyval._bool_expression) = (yysemantic_stack_[(3) - (2)]._bool_expression); 
 }
    break;

  case 329:

/* Line 690 of lalr1.cc  */
#line 2000 "parser/nssis_new.yy"
    { 
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._bool_expression));
 }
    break;

  case 330:

/* Line 690 of lalr1.cc  */
#line 2005 "parser/nssis_new.yy"
    { 
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._bool_expression));
 }
    break;

  case 331:

/* Line 690 of lalr1.cc  */
#line 2010 "parser/nssis_new.yy"
    { 
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._bool_expression));
 }
    break;

  case 332:

/* Line 690 of lalr1.cc  */
#line 2015 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._bool_expression)!=NULL && (yysemantic_stack_[(3) - (3)]._bool_expression)!=NULL)
    (yyval._bool_expression) = new bool_expression(1, (yysemantic_stack_[(3) - (1)]._bool_expression), (yysemantic_stack_[(3) - (3)]._bool_expression));
  else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 333:

/* Line 690 of lalr1.cc  */
#line 2021 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._bool_expression)!=NULL && (yysemantic_stack_[(3) - (3)]._bool_expression)!=NULL)
    (yyval._bool_expression) = new bool_expression(2, (yysemantic_stack_[(3) - (1)]._bool_expression), (yysemantic_stack_[(3) - (3)]._bool_expression));
  else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 334:

/* Line 690 of lalr1.cc  */
#line 2027 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)]._bool_expression));
  USE((yysemantic_stack_[(3) - (3)]._bool_expression));
 }
    break;

  case 335:

/* Line 690 of lalr1.cc  */
#line 2033 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)]._bool_expression)!=NULL)
    (yyval._bool_expression) = new bool_expression(3, (yysemantic_stack_[(2) - (2)]._bool_expression));
  else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 336:

/* Line 690 of lalr1.cc  */
#line 2039 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(2) - (2)]._bool_expression));
 }
    break;

  case 337:

/* Line 690 of lalr1.cc  */
#line 2044 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._expression)!=NULL && (yysemantic_stack_[(3) - (3)]._expression)!=NULL) {
    logic_expression *expr = new logic_expression((yysemantic_stack_[(3) - (2)]._unsigned_char), (yysemantic_stack_[(3) - (1)]._expression), (yysemantic_stack_[(3) - (3)]._expression));
    (yyval._bool_expression) = new bool_expression(0,  expr);
  } else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 338:

/* Line 690 of lalr1.cc  */
#line 2051 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (3)].sval)!=NULL) {
    laction *a = new laction();
    variable *v;
    int i = search_string_table((yysemantic_stack_[(3) - (3)].sval));
    if(i>=0) {
      v = new variable((*string_table)[i]);
      free((yysemantic_stack_[(3) - (3)].sval));
    } else {
      v = new variable((yysemantic_stack_[(3) - (3)].sval));
      string_table->push_back((yysemantic_stack_[(3) - (3)].sval));
    }
    logic_expression *expr = new logic_expression(0, a, v);
    (yyval._bool_expression) = new bool_expression(0,  expr);
  } else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 339:

/* Line 690 of lalr1.cc  */
#line 2068 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (3)].sval));
 }
    break;

  case 340:

/* Line 690 of lalr1.cc  */
#line 2073 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (3)].sval));
 }
    break;

  case 341:

/* Line 690 of lalr1.cc  */
#line 2078 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(2) - (2)].sval));
 }
    break;

  case 342:

/* Line 690 of lalr1.cc  */
#line 2083 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(5) - (1)].sval)!=NULL && (yysemantic_stack_[(5) - (5)].sval)!=NULL) {
    laction *a;
    int i = search_string_table((yysemantic_stack_[(5) - (1)].sval));
    if(i>=0) {
      a = new laction((*string_table)[i]);
      free((yysemantic_stack_[(5) - (1)].sval));
    } else {
      a = new laction((yysemantic_stack_[(5) - (1)].sval));
      string_table->push_back((yysemantic_stack_[(5) - (1)].sval));
    }
    variable *v;
    int j = search_string_table((yysemantic_stack_[(5) - (5)].sval));
    if(j>=0) {
      if(i>=0)
	v = new variable((*string_table)[i], (*string_table)[j]);
      else
	v = new variable((yysemantic_stack_[(5) - (1)].sval), (*string_table)[j]);
      free((yysemantic_stack_[(5) - (5)].sval));
    } else {
      if(i>=0)
	v = new variable((*string_table)[i], (yysemantic_stack_[(5) - (5)].sval));
      else
	v = new variable((yysemantic_stack_[(5) - (1)].sval), (yysemantic_stack_[(5) - (5)].sval));
      string_table->push_back((yysemantic_stack_[(5) - (5)].sval));
    }
    i = search_logic_expression_table(a, v);
    if(i>=0) {
      (yyval._bool_expression) = (*logic_expression_table)[i];
      delete a;
      delete v;
    } else {
			logic_expression *expr = new logic_expression(0, a, v);
			bool_expression *bexpr = new bool_expression(0,  expr);
      (yyval._bool_expression) = bexpr;
      logic_expression_table->push_back(bexpr);
    }
  } else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 343:

/* Line 690 of lalr1.cc  */
#line 2123 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (1)].sval));
  USE((yysemantic_stack_[(5) - (5)].sval));
 }
    break;

  case 344:

/* Line 690 of lalr1.cc  */
#line 2129 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (1)].sval));
  USE((yysemantic_stack_[(5) - (5)].sval));
 }
    break;

  case 345:

/* Line 690 of lalr1.cc  */
#line 2135 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (1)].sval));
  USE((yysemantic_stack_[(5) - (5)].sval));
 }
    break;

  case 346:

/* Line 690 of lalr1.cc  */
#line 2141 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(4) - (1)].sval));
  USE((yysemantic_stack_[(4) - (4)].sval));
 }
    break;

  case 347:

/* Line 690 of lalr1.cc  */
#line 2147 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(4) - (1)].sval));
  USE((yysemantic_stack_[(4) - (4)].sval));
 }
    break;

  case 348:

/* Line 690 of lalr1.cc  */
#line 2153 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (1)].sval));
  USE((yysemantic_stack_[(5) - (5)].sval));
 }
    break;

  case 349:

/* Line 690 of lalr1.cc  */
#line 2159 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)].sval));
  USE((yysemantic_stack_[(3) - (3)].sval));
 }
    break;

  case 350:

/* Line 690 of lalr1.cc  */
#line 2165 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 351:

/* Line 690 of lalr1.cc  */
#line 2170 "parser/nssis_new.yy"
    {
  (yyval._unsigned_char) = 2;
 }
    break;

  case 352:

/* Line 690 of lalr1.cc  */
#line 2173 "parser/nssis_new.yy"
    {
  (yyval._unsigned_char) = 3;
  }
    break;

  case 353:

/* Line 690 of lalr1.cc  */
#line 2176 "parser/nssis_new.yy"
    {
  (yyval._unsigned_char) = 4;
  }
    break;

  case 354:

/* Line 690 of lalr1.cc  */
#line 2179 "parser/nssis_new.yy"
    {
  (yyval._unsigned_char) = 5;
  }
    break;

  case 355:

/* Line 690 of lalr1.cc  */
#line 2182 "parser/nssis_new.yy"
    {
  (yyval._unsigned_char) = 0;
  }
    break;

  case 356:

/* Line 690 of lalr1.cc  */
#line 2185 "parser/nssis_new.yy"
    {
  (yyval._unsigned_char) = 1;
  }
    break;

  case 357:

/* Line 690 of lalr1.cc  */
#line 2190 "parser/nssis_new.yy"
    { 
  (yyval._bool_expression) = (yysemantic_stack_[(3) - (2)]._bool_expression); 
 }
    break;

  case 358:

/* Line 690 of lalr1.cc  */
#line 2193 "parser/nssis_new.yy"
    { 
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._bool_expression));
 }
    break;

  case 359:

/* Line 690 of lalr1.cc  */
#line 2198 "parser/nssis_new.yy"
    { 
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._bool_expression));
 }
    break;

  case 360:

/* Line 690 of lalr1.cc  */
#line 2203 "parser/nssis_new.yy"
    { 
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._bool_expression));
 }
    break;

  case 361:

/* Line 690 of lalr1.cc  */
#line 2208 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._bool_expression)!=NULL && (yysemantic_stack_[(3) - (3)]._bool_expression)!=NULL)
    (yyval._bool_expression) = new bool_expression(1, (yysemantic_stack_[(3) - (1)]._bool_expression), (yysemantic_stack_[(3) - (3)]._bool_expression));
  else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 362:

/* Line 690 of lalr1.cc  */
#line 2214 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._bool_expression)!=NULL && (yysemantic_stack_[(3) - (3)]._bool_expression)!=NULL)
    (yyval._bool_expression) = new bool_expression(2, (yysemantic_stack_[(3) - (1)]._bool_expression), (yysemantic_stack_[(3) - (3)]._bool_expression));
  else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 363:

/* Line 690 of lalr1.cc  */
#line 2220 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)]._bool_expression));
  USE((yysemantic_stack_[(3) - (3)]._bool_expression));
 }
    break;

  case 364:

/* Line 690 of lalr1.cc  */
#line 2226 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)]._bool_expression)!=NULL)
    (yyval._bool_expression) = new bool_expression(3, (yysemantic_stack_[(2) - (2)]._bool_expression));
  else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 365:

/* Line 690 of lalr1.cc  */
#line 2232 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(2) - (2)]._bool_expression));
 }
    break;

  case 366:

/* Line 690 of lalr1.cc  */
#line 2237 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._expression)!=NULL && (yysemantic_stack_[(3) - (3)]._expression)!=NULL) {
    logic_expression *expr = new logic_expression((yysemantic_stack_[(3) - (2)]._unsigned_char), (yysemantic_stack_[(3) - (1)]._expression), (yysemantic_stack_[(3) - (3)]._expression));
    (yyval._bool_expression) = new bool_expression(0,  expr);
  } else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 367:

/* Line 690 of lalr1.cc  */
#line 2244 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (3)].sval)!=NULL) {
    laction *a = new laction();
    variable *v;
    int i = search_string_table((yysemantic_stack_[(3) - (3)].sval));
    if(i>=0) {
      v = new variable((*string_table)[i]);
      free((yysemantic_stack_[(3) - (3)].sval));
    } else {
      v = new variable((yysemantic_stack_[(3) - (3)].sval));
      string_table->push_back((yysemantic_stack_[(3) - (3)].sval));
    }
    logic_expression *expr = new logic_expression(0, a, v);
    (yyval._bool_expression) = new bool_expression(0,  expr);
  } else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 368:

/* Line 690 of lalr1.cc  */
#line 2261 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (3)].sval));
 }
    break;

  case 369:

/* Line 690 of lalr1.cc  */
#line 2266 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (3)].sval));
 }
    break;

  case 370:

/* Line 690 of lalr1.cc  */
#line 2271 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(2) - (2)].sval));
 }
    break;

  case 371:

/* Line 690 of lalr1.cc  */
#line 2276 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(5) - (1)].sval)!=NULL && (yysemantic_stack_[(5) - (5)].sval)!=NULL) {
    laction *a;
    int i = search_string_table((yysemantic_stack_[(5) - (1)].sval));
    if(i>=0) {
      a = new laction((*string_table)[i]);
      free((yysemantic_stack_[(5) - (1)].sval));
    } else {
      a = new laction((yysemantic_stack_[(5) - (1)].sval));
      string_table->push_back((yysemantic_stack_[(5) - (1)].sval));
    }
    variable *v;
    int j = search_string_table((yysemantic_stack_[(5) - (5)].sval));
    if(j>=0) {
      if(i>=0)
	v = new variable((*string_table)[i], (*string_table)[j]);
      else
	v = new variable((yysemantic_stack_[(5) - (1)].sval), (*string_table)[j]);
      free((yysemantic_stack_[(5) - (5)].sval));
    } else {
      if(i>=0)
	v = new variable((*string_table)[i], (yysemantic_stack_[(5) - (5)].sval));
      else
	v = new variable((yysemantic_stack_[(5) - (1)].sval), (yysemantic_stack_[(5) - (5)].sval));
      string_table->push_back((yysemantic_stack_[(5) - (5)].sval));
    }
    logic_expression *expr = new logic_expression(0, a, v);
    (yyval._bool_expression) = new bool_expression(0,  expr);
  } else 
    (yyval._bool_expression) = NULL;
 }
    break;

  case 372:

/* Line 690 of lalr1.cc  */
#line 2307 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (1)].sval));
  USE((yysemantic_stack_[(5) - (5)].sval));
 }
    break;

  case 373:

/* Line 690 of lalr1.cc  */
#line 2313 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (1)].sval));
  USE((yysemantic_stack_[(5) - (5)].sval));
 }
    break;

  case 374:

/* Line 690 of lalr1.cc  */
#line 2319 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (1)].sval));
  USE((yysemantic_stack_[(5) - (5)].sval));
 }
    break;

  case 375:

/* Line 690 of lalr1.cc  */
#line 2325 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(4) - (1)].sval));
  USE((yysemantic_stack_[(4) - (4)].sval));
 }
    break;

  case 376:

/* Line 690 of lalr1.cc  */
#line 2331 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(4) - (1)].sval));
  USE((yysemantic_stack_[(4) - (4)].sval));
 }
    break;

  case 377:

/* Line 690 of lalr1.cc  */
#line 2337 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (1)].sval));
  USE((yysemantic_stack_[(5) - (5)].sval));
 }
    break;

  case 378:

/* Line 690 of lalr1.cc  */
#line 2343 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)].sval));
  USE((yysemantic_stack_[(3) - (3)].sval));
 }
    break;

  case 379:

/* Line 690 of lalr1.cc  */
#line 2349 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(5) - (5)].sval)!=NULL) {
    laction *a = new laction((*string_table)[0]);
    variable *v;
    int j = search_string_table((yysemantic_stack_[(5) - (5)].sval));
    if(j>=0) {
      v = new variable((*string_table)[0], (*string_table)[j]);
      free((yysemantic_stack_[(5) - (5)].sval));
    } else { 
      v = new variable((*string_table)[0], (yysemantic_stack_[(5) - (5)].sval));
      string_table->push_back((yysemantic_stack_[(5) - (5)].sval));
    }
    logic_expression *expr = new logic_expression(0, a, v);
    (yyval._bool_expression) = new bool_expression(0,  expr);
  } else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 380:

/* Line 690 of lalr1.cc  */
#line 2366 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (5)].sval));
 }
    break;

  case 381:

/* Line 690 of lalr1.cc  */
#line 2371 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (5)].sval));
 }
    break;

  case 382:

/* Line 690 of lalr1.cc  */
#line 2376 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(4) - (4)].sval));
 }
    break;

  case 383:

/* Line 690 of lalr1.cc  */
#line 2381 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(4) - (4)].sval));
 }
    break;

  case 384:

/* Line 690 of lalr1.cc  */
#line 2386 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (5)].sval));
 }
    break;

  case 385:

/* Line 690 of lalr1.cc  */
#line 2391 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (3)].sval));
 }
    break;

  case 386:

/* Line 690 of lalr1.cc  */
#line 2396 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 387:

/* Line 690 of lalr1.cc  */
#line 2402 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(1) - (1)]._bool_value);
 }
    break;

  case 388:

/* Line 690 of lalr1.cc  */
#line 2405 "parser/nssis_new.yy"
    {
    int i = search_string_table((yysemantic_stack_[(1) - (1)].sval));
    if(i>=0) {
      (yyval._expression) = new variable((*string_table)[i]);
      free((yysemantic_stack_[(1) - (1)].sval));
    } else {
      (yyval._expression) = new variable((yysemantic_stack_[(1) - (1)].sval)); // can be enumerate value. Will be decided during global syntax checking
      string_table->push_back((yysemantic_stack_[(1) - (1)].sval));
    }
  }
    break;

  case 389:

/* Line 690 of lalr1.cc  */
#line 2415 "parser/nssis_new.yy"
    {
  (yyval._expression) = new int_value((yysemantic_stack_[(1) - (1)].ival));
  }
    break;

  case 390:

/* Line 690 of lalr1.cc  */
#line 2418 "parser/nssis_new.yy"
    {
  (yyval._bool_value) = new bool_value(true);
  }
    break;

  case 391:

/* Line 690 of lalr1.cc  */
#line 2421 "parser/nssis_new.yy"
    {
  (yyval._bool_value) = new bool_value(false);
  }
    break;

  case 392:

/* Line 690 of lalr1.cc  */
#line 2425 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(1) - (1)]._bool_value);
 }
    break;

  case 393:

/* Line 690 of lalr1.cc  */
#line 2428 "parser/nssis_new.yy"
    {
    int i = search_string_table((yysemantic_stack_[(1) - (1)].sval));
    if(i>=0) {
      (yyval._expression) = new variable((*string_table)[i]);
      free((yysemantic_stack_[(1) - (1)].sval));
    } else {
      (yyval._expression) = new variable((yysemantic_stack_[(1) - (1)].sval)); // can be enumerate value. Will be decided during global syntax checking
      string_table->push_back((yysemantic_stack_[(1) - (1)].sval));
    }
  }
    break;

  case 394:

/* Line 690 of lalr1.cc  */
#line 2438 "parser/nssis_new.yy"
    {
    int i = search_string_table((yysemantic_stack_[(3) - (3)].sval));
    variable *var;
    if(i>=0) {
      var = new variable((*string_table)[0], (*string_table)[i]);
      free((yysemantic_stack_[(3) - (3)].sval));
    } else {
      var = new variable((*string_table)[0], (yysemantic_stack_[(3) - (3)].sval)); 
      string_table->push_back((yysemantic_stack_[(3) - (3)].sval));
    }
    i = search_variable_table(var);
    if(i>=0) {
      (yyval._expression) = (*variable_table)[i];
      delete var;
    } else {
      (yyval._expression) = var;
      variable_table->push_back(var);
    }
  }
    break;

  case 395:

/* Line 690 of lalr1.cc  */
#line 2457 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (3)].sval));
  }
    break;

  case 396:

/* Line 690 of lalr1.cc  */
#line 2462 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (3)].sval));
  }
    break;

  case 397:

/* Line 690 of lalr1.cc  */
#line 2467 "parser/nssis_new.yy"
    {
  (yyval._expression) = new int_value((yysemantic_stack_[(1) - (1)].ival));
  }
    break;

  case 398:

/* Line 690 of lalr1.cc  */
#line 2470 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(1) - (1)]._bool_value);
 }
    break;

  case 399:

/* Line 690 of lalr1.cc  */
#line 2473 "parser/nssis_new.yy"
    {
    int i = search_string_table((yysemantic_stack_[(1) - (1)].sval));
    if(i>=0) {
      (yyval._expression) = new variable((*string_table)[i]);
      free((yysemantic_stack_[(1) - (1)].sval));
    } else {
      (yyval._expression) = new variable((yysemantic_stack_[(1) - (1)].sval)); // can be enumerate value. Will be decided during global syntax checking
      string_table->push_back((yysemantic_stack_[(1) - (1)].sval));
    }
  }
    break;

  case 400:

/* Line 690 of lalr1.cc  */
#line 2483 "parser/nssis_new.yy"
    {
    int i = search_string_table((yysemantic_stack_[(3) - (1)].sval));
    int j = search_string_table((yysemantic_stack_[(3) - (3)].sval));
    variable *var;
    if(i>=0) {
      if(j>=0) {
	var = new variable((*string_table)[i], (*string_table)[j]);
	free((yysemantic_stack_[(3) - (3)].sval));
      } else {
	var = new variable((*string_table)[i], (yysemantic_stack_[(3) - (3)].sval));
	string_table->push_back((yysemantic_stack_[(3) - (3)].sval));
      }
      free((yysemantic_stack_[(3) - (1)].sval));
    } else {
      if(j>=0) {
	var = new variable((yysemantic_stack_[(3) - (1)].sval), (*string_table)[j]);
	free((yysemantic_stack_[(3) - (3)].sval));
      } else {
	var = new variable((yysemantic_stack_[(3) - (1)].sval), (yysemantic_stack_[(3) - (3)].sval));
	string_table->push_back((yysemantic_stack_[(3) - (3)].sval));
      }
      string_table->push_back((yysemantic_stack_[(3) - (1)].sval));
    }
    i = search_variable_table(var);
    if(i>=0) {
      (yyval._expression) = (*variable_table)[i];
      delete var;
    } else {
      (yyval._expression) = var;
      variable_table->push_back(var);
    }
  }
    break;

  case 401:

/* Line 690 of lalr1.cc  */
#line 2515 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)].sval));
  USE((yysemantic_stack_[(3) - (3)].sval));
  }
    break;

  case 402:

/* Line 690 of lalr1.cc  */
#line 2521 "parser/nssis_new.yy"
    {
    int i = search_string_table((yysemantic_stack_[(3) - (3)].sval));
    variable *var;
    if(i>=0) {
      var = new variable((*string_table)[0], (*string_table)[i]);
      free((yysemantic_stack_[(3) - (3)].sval));
    } else {
      var = new variable((*string_table)[0], (yysemantic_stack_[(3) - (3)].sval)); 
      string_table->push_back((yysemantic_stack_[(3) - (3)].sval));
    }
    i = search_variable_table(var);
    if(i>=0) {
      (yyval._expression) = (*variable_table)[i];
      delete var;
    } else {
      (yyval._expression) = var;
      variable_table->push_back(var);
    }
  }
    break;

  case 403:

/* Line 690 of lalr1.cc  */
#line 2540 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (3)].sval));
  }
    break;

  case 404:

/* Line 690 of lalr1.cc  */
#line 2545 "parser/nssis_new.yy"
    {
  (yyval._expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (3)].sval));
  }
    break;

  case 405:

/* Line 690 of lalr1.cc  */
#line 2550 "parser/nssis_new.yy"
    {
  (yyval._expression) = new int_value((yysemantic_stack_[(1) - (1)].ival));
  }
    break;

  case 406:

/* Line 690 of lalr1.cc  */
#line 2554 "parser/nssis_new.yy"
    {
  (yyval._expression) = (yysemantic_stack_[(1) - (1)]._bool_value);
 }
    break;

  case 407:

/* Line 690 of lalr1.cc  */
#line 2557 "parser/nssis_new.yy"
    {
    int i = search_string_table((yysemantic_stack_[(1) - (1)].sval));
    if(i>=0) {
      (yyval._expression) = new enum_value((*string_table)[i]);
      free((yysemantic_stack_[(1) - (1)].sval));
    } else {
      (yyval._expression) = new enum_value((yysemantic_stack_[(1) - (1)].sval)); // can be enumerate value. Will be decided during global syntax checking
      string_table->push_back((yysemantic_stack_[(1) - (1)].sval));
    }
  }
    break;

  case 408:

/* Line 690 of lalr1.cc  */
#line 2567 "parser/nssis_new.yy"
    {
  (yyval._expression) = new int_value((yysemantic_stack_[(1) - (1)].ival));
  }
    break;

  case 409:

/* Line 690 of lalr1.cc  */
#line 2572 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 410:

/* Line 690 of lalr1.cc  */
#line 2575 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 411:

/* Line 690 of lalr1.cc  */
#line 2578 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 412:

/* Line 690 of lalr1.cc  */
#line 2582 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 413:

/* Line 690 of lalr1.cc  */
#line 2586 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
  }
    break;

  case 415:

/* Line 690 of lalr1.cc  */
#line 2591 "parser/nssis_new.yy"
    {
  driver.syntax_error = true;
  }
    break;

  case 416:

/* Line 690 of lalr1.cc  */
#line 2595 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(4) - (1)].sval)!=NULL && (yysemantic_stack_[(4) - (3)]._bool_expression)!=NULL) {
    (*is_evaluation)[*(yysemantic_stack_[(4) - (1)].sval)] = (yysemantic_stack_[(4) - (3)]._bool_expression);
    free((yysemantic_stack_[(4) - (1)].sval));
  } 
 }
    break;

  case 417:

/* Line 690 of lalr1.cc  */
#line 2601 "parser/nssis_new.yy"
    {
  driver.syntax_error = true;
  USE((yysemantic_stack_[(4) - (1)].sval));
  USE((yysemantic_stack_[(4) - (3)]._bool_expression));
 }
    break;

  case 418:

/* Line 690 of lalr1.cc  */
#line 2606 "parser/nssis_new.yy"
    {
  driver.syntax_error = true;
  USE((yysemantic_stack_[(4) - (1)].sval));
  USE((yysemantic_stack_[(4) - (3)]._bool_expression));
 }
    break;

  case 419:

/* Line 690 of lalr1.cc  */
#line 2611 "parser/nssis_new.yy"
    {
  driver.syntax_error = true;
  USE((yysemantic_stack_[(4) - (1)].sval));
  USE((yysemantic_stack_[(4) - (3)]._bool_expression));
 }
    break;

  case 420:

/* Line 690 of lalr1.cc  */
#line 2616 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(5) - (2)].sval)!=NULL && (yysemantic_stack_[(5) - (4)]._bool_expression)!=NULL) {
    if(is_evaluation->find(*(yysemantic_stack_[(5) - (2)].sval)) != is_evaluation->end() && options["quiet"] == 0)
      cout << "warning: atomic proposition " << *(yysemantic_stack_[(5) - (2)].sval) << " has already been defined." << endl;
    (*is_evaluation)[*(yysemantic_stack_[(5) - (2)].sval)] = (yysemantic_stack_[(5) - (4)]._bool_expression);
    free((yysemantic_stack_[(5) - (2)].sval));
  }
 }
    break;

  case 421:

/* Line 690 of lalr1.cc  */
#line 2624 "parser/nssis_new.yy"
    {
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._bool_expression));
 }
    break;

  case 422:

/* Line 690 of lalr1.cc  */
#line 2629 "parser/nssis_new.yy"
    {
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._bool_expression));
 }
    break;

  case 423:

/* Line 690 of lalr1.cc  */
#line 2634 "parser/nssis_new.yy"
    {
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._bool_expression));
 }
    break;

  case 424:

/* Line 690 of lalr1.cc  */
#line 2639 "parser/nssis_new.yy"
    {
  driver.syntax_error = true;
  }
    break;

  case 425:

/* Line 690 of lalr1.cc  */
#line 2643 "parser/nssis_new.yy"
    { 
  (yyval._bool_expression) = (yysemantic_stack_[(3) - (2)]._bool_expression); 
 }
    break;

  case 426:

/* Line 690 of lalr1.cc  */
#line 2646 "parser/nssis_new.yy"
    { 
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._bool_expression));
 }
    break;

  case 427:

/* Line 690 of lalr1.cc  */
#line 2651 "parser/nssis_new.yy"
    { 
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._bool_expression));
 }
    break;

  case 428:

/* Line 690 of lalr1.cc  */
#line 2656 "parser/nssis_new.yy"
    { 
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._bool_expression));
 }
    break;

  case 429:

/* Line 690 of lalr1.cc  */
#line 2661 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._bool_expression)!=NULL && (yysemantic_stack_[(3) - (3)]._bool_expression)!=NULL)
    (yyval._bool_expression) = new bool_expression(1, (yysemantic_stack_[(3) - (1)]._bool_expression), (yysemantic_stack_[(3) - (3)]._bool_expression));
  else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 430:

/* Line 690 of lalr1.cc  */
#line 2667 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._bool_expression)!=NULL && (yysemantic_stack_[(3) - (3)]._bool_expression)!=NULL)
    (yyval._bool_expression) = new bool_expression(2, (yysemantic_stack_[(3) - (1)]._bool_expression), (yysemantic_stack_[(3) - (3)]._bool_expression));
  else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 431:

/* Line 690 of lalr1.cc  */
#line 2673 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)]._bool_expression));USE((yysemantic_stack_[(3) - (3)]._bool_expression));
 }
    break;

  case 432:

/* Line 690 of lalr1.cc  */
#line 2678 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)]._bool_expression)!=NULL)
    (yyval._bool_expression) = new bool_expression(3, (yysemantic_stack_[(2) - (2)]._bool_expression));
  else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 433:

/* Line 690 of lalr1.cc  */
#line 2684 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(2) - (2)]._bool_expression));
 }
    break;

  case 434:

/* Line 690 of lalr1.cc  */
#line 2689 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._expression)!=NULL && (yysemantic_stack_[(3) - (3)]._expression)!=NULL) {
    logic_expression *expr = new logic_expression((yysemantic_stack_[(3) - (2)]._unsigned_char), (yysemantic_stack_[(3) - (1)]._expression), (yysemantic_stack_[(3) - (3)]._expression));
    (yyval._bool_expression) = new bool_expression(0,  expr);
  } else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 435:

/* Line 690 of lalr1.cc  */
#line 2696 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 436:

/* Line 690 of lalr1.cc  */
#line 2704 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 437:

/* Line 690 of lalr1.cc  */
#line 2707 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 438:

/* Line 690 of lalr1.cc  */
#line 2711 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 439:

/* Line 690 of lalr1.cc  */
#line 2714 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 440:

/* Line 690 of lalr1.cc  */
#line 2718 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 441:

/* Line 690 of lalr1.cc  */
#line 2722 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 442:

/* Line 690 of lalr1.cc  */
#line 2726 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 443:

/* Line 690 of lalr1.cc  */
#line 2730 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 444:

/* Line 690 of lalr1.cc  */
#line 2734 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 445:

/* Line 690 of lalr1.cc  */
#line 2738 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
  }
    break;

  case 446:

/* Line 690 of lalr1.cc  */
#line 2742 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].ival)==1 && (yysemantic_stack_[(3) - (3)].ival)==1)
    is_istates = (yysemantic_stack_[(3) - (2)]._bool_expression); 
 }
    break;

  case 447:

/* Line 690 of lalr1.cc  */
#line 2746 "parser/nssis_new.yy"
    {
  driver.syntax_error = true;
  }
    break;

  case 448:

/* Line 690 of lalr1.cc  */
#line 2750 "parser/nssis_new.yy"
    { 
  (yyval._bool_expression) = (yysemantic_stack_[(3) - (2)]._bool_expression); 
}
    break;

  case 449:

/* Line 690 of lalr1.cc  */
#line 2753 "parser/nssis_new.yy"
    { 
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._bool_expression));
 }
    break;

  case 450:

/* Line 690 of lalr1.cc  */
#line 2758 "parser/nssis_new.yy"
    { 
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._bool_expression));
 }
    break;

  case 451:

/* Line 690 of lalr1.cc  */
#line 2763 "parser/nssis_new.yy"
    { 
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._bool_expression))
 }
    break;

  case 452:

/* Line 690 of lalr1.cc  */
#line 2768 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._bool_expression)!=NULL && (yysemantic_stack_[(3) - (3)]._bool_expression)!=NULL)
    (yyval._bool_expression) = new bool_expression(1, (yysemantic_stack_[(3) - (1)]._bool_expression), (yysemantic_stack_[(3) - (3)]._bool_expression));
  else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 453:

/* Line 690 of lalr1.cc  */
#line 2774 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._bool_expression)!=NULL && (yysemantic_stack_[(3) - (3)]._bool_expression)!=NULL)
    (yyval._bool_expression) = new bool_expression(2, (yysemantic_stack_[(3) - (1)]._bool_expression), (yysemantic_stack_[(3) - (3)]._bool_expression));
  else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 454:

/* Line 690 of lalr1.cc  */
#line 2780 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)]._bool_expression));USE((yysemantic_stack_[(3) - (3)]._bool_expression));
 }
    break;

  case 455:

/* Line 690 of lalr1.cc  */
#line 2785 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)]._bool_expression)!=NULL)
    (yyval._bool_expression) = new bool_expression(3, (yysemantic_stack_[(2) - (2)]._bool_expression));
  else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 456:

/* Line 690 of lalr1.cc  */
#line 2791 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(2) - (2)]._bool_expression));
 }
    break;

  case 457:

/* Line 690 of lalr1.cc  */
#line 2796 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(7) - (1)].sval)!=NULL && (yysemantic_stack_[(7) - (3)].sval)!=NULL && (yysemantic_stack_[(7) - (5)].sval)!=NULL && (yysemantic_stack_[(7) - (7)].sval)!=NULL) {
    int i = search_string_table((yysemantic_stack_[(7) - (1)].sval));
    int j = search_string_table((yysemantic_stack_[(7) - (3)].sval));
    variable *v;
    if(i>=0) {
      if(j>=0) {
	v = new variable((*string_table)[i], (*string_table)[j]);
	free((yysemantic_stack_[(7) - (3)].sval));
      } else {
	v = new variable((*string_table)[i], (yysemantic_stack_[(7) - (3)].sval));
	string_table->push_back((yysemantic_stack_[(7) - (3)].sval));
      }
      free((yysemantic_stack_[(7) - (1)].sval));
    } else {
      if(j>=0) {
	v = new variable((yysemantic_stack_[(7) - (1)].sval), (*string_table)[j]);
	free((yysemantic_stack_[(7) - (3)].sval));
      } else {
	v = new variable((yysemantic_stack_[(7) - (1)].sval), (yysemantic_stack_[(7) - (3)].sval));
	string_table->push_back((yysemantic_stack_[(7) - (3)].sval));
      }
      string_table->push_back((yysemantic_stack_[(7) - (1)].sval));
    }
    i = search_variable_table(v);
    if(i>=0) {
      delete v;
      v = (*variable_table)[i];
    } else {
      variable_table->push_back(v);
    }

    i = search_string_table((yysemantic_stack_[(7) - (5)].sval));
    j = search_string_table((yysemantic_stack_[(7) - (7)].sval));
    variable *v1;
    if(i>=0) {
      if(j>=0) {
	v1 = new variable((*string_table)[i], (*string_table)[j]);
	free((yysemantic_stack_[(7) - (7)].sval));
      } else {
	v1 = new variable((*string_table)[i], (yysemantic_stack_[(7) - (7)].sval));
	string_table->push_back((yysemantic_stack_[(7) - (7)].sval));
      }
      free((yysemantic_stack_[(7) - (5)].sval));
    } else {
      if(j>=0) {
	v1 = new variable((yysemantic_stack_[(7) - (5)].sval), (*string_table)[j]);
	free((yysemantic_stack_[(7) - (7)].sval));
      } else {
	v1 = new variable((yysemantic_stack_[(7) - (5)].sval), (yysemantic_stack_[(7) - (7)].sval));
	string_table->push_back((yysemantic_stack_[(7) - (7)].sval));
      }
      string_table->push_back((yysemantic_stack_[(7) - (5)].sval));
    }
    i = search_variable_table(v1);
    if(i>=0) {
      delete v1;
      v1 = (*variable_table)[i];
    } else {
      variable_table->push_back(v1);
    }

    i = search_logic_expression_table1(v, v1);
    if(i>=0) {
      (yyval._bool_expression) = (*logic_expression_table1)[i];
      free((yysemantic_stack_[(7) - (5)].sval));
    } else {
			logic_expression *e = new logic_expression(0, v, v1);
			bool_expression *bexpr = new bool_expression(0, e);
      (yyval._bool_expression) = bexpr;
      logic_expression_table1->push_back(bexpr);
    }    
  } else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 458:

/* Line 690 of lalr1.cc  */
#line 2871 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(7) - (1)].sval)!=NULL && (yysemantic_stack_[(7) - (3)].sval)!=NULL && (yysemantic_stack_[(7) - (7)].sval)!=NULL) {
    int i = search_string_table((yysemantic_stack_[(7) - (1)].sval));
    int j = search_string_table((yysemantic_stack_[(7) - (3)].sval));
    variable *v;
    if(i>=0) {
      if(j>=0) {
	v = new variable((*string_table)[i], (*string_table)[j]);
	free((yysemantic_stack_[(7) - (3)].sval));
      } else {
	v = new variable((*string_table)[i], (yysemantic_stack_[(7) - (3)].sval));
	string_table->push_back((yysemantic_stack_[(7) - (3)].sval));
      }
      free((yysemantic_stack_[(7) - (1)].sval));
    } else {
      if(j>=0) {
	v = new variable((yysemantic_stack_[(7) - (1)].sval), (*string_table)[j]);
	free((yysemantic_stack_[(7) - (3)].sval));
      } else {
	v = new variable((yysemantic_stack_[(7) - (1)].sval), (yysemantic_stack_[(7) - (3)].sval));
	string_table->push_back((yysemantic_stack_[(7) - (3)].sval));
      }
      string_table->push_back((yysemantic_stack_[(7) - (1)].sval));
    }
    i = search_variable_table(v);
    if(i>=0) {
      delete v;
      v = (*variable_table)[i];
    } else {
      variable_table->push_back(v);
    }

    j = search_string_table((yysemantic_stack_[(7) - (7)].sval));
    variable *v1;
    if(j>=0) {
      v1 = new variable((*string_table)[0], (*string_table)[j]);
      free((yysemantic_stack_[(7) - (7)].sval));
    } else {
      v1 = new variable((*string_table)[0], (yysemantic_stack_[(7) - (7)].sval));
      string_table->push_back((yysemantic_stack_[(7) - (7)].sval));
    }
    
    i = search_variable_table(v1);
    if(i>=0) {
      delete v1;
      v1 = (*variable_table)[i];
    } else {
      variable_table->push_back(v1);
    }

    i = search_logic_expression_table1(v, v1);
    if(i>=0) {
      (yyval._bool_expression) = (*logic_expression_table1)[i];
    } else {
			logic_expression *e = new logic_expression(0, v, v1);
			bool_expression *bexpr = new bool_expression(0, e);
      (yyval._bool_expression) = bexpr;
      logic_expression_table1->push_back(bexpr);
    }    
  } else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 459:

/* Line 690 of lalr1.cc  */
#line 2933 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(7) - (3)].sval)!=NULL && (yysemantic_stack_[(7) - (5)].sval)!=NULL && (yysemantic_stack_[(7) - (7)].sval)!=NULL) {
    int j = search_string_table((yysemantic_stack_[(7) - (3)].sval));
    variable *v;
    if(j>=0) {
      v = new variable((*string_table)[0], (*string_table)[j]);
      free((yysemantic_stack_[(7) - (3)].sval));
    } else {
      v = new variable((*string_table)[0], (yysemantic_stack_[(7) - (3)].sval));
      string_table->push_back((yysemantic_stack_[(7) - (3)].sval));
    }
    int i = search_variable_table(v);
    if(i>=0) {
      delete v;
      v = (*variable_table)[i];
    } else {
      variable_table->push_back(v);
    }

    i = search_string_table((yysemantic_stack_[(7) - (5)].sval));
    j = search_string_table((yysemantic_stack_[(7) - (7)].sval));
    variable *v1;
    if(i>=0) {
      if(j>=0) {
	v1 = new variable((*string_table)[i], (*string_table)[j]);
	free((yysemantic_stack_[(7) - (7)].sval));
      } else {
	v1 = new variable((*string_table)[i], (yysemantic_stack_[(7) - (7)].sval));
	string_table->push_back((yysemantic_stack_[(7) - (7)].sval));
      }
      free((yysemantic_stack_[(7) - (5)].sval));
    } else {
      if(j>=0) {
	v1 = new variable((yysemantic_stack_[(7) - (5)].sval), (*string_table)[j]);
	free((yysemantic_stack_[(7) - (7)].sval));
      } else {
	v1 = new variable((yysemantic_stack_[(7) - (5)].sval), (yysemantic_stack_[(7) - (7)].sval));
	string_table->push_back((yysemantic_stack_[(7) - (7)].sval));
      }
      string_table->push_back((yysemantic_stack_[(7) - (5)].sval));
    }
    i = search_variable_table(v1);
    if(i>=0) {
      delete v1;
      v1 = (*variable_table)[i];
    } else {
      variable_table->push_back(v1);
    }

    i = search_logic_expression_table1(v, v1);
    if(i>=0) {
      (yyval._bool_expression) = (*logic_expression_table1)[i];
      free((yysemantic_stack_[(7) - (5)].sval));
    } else {
			logic_expression *e = new logic_expression(0, v, v1);
			bool_expression *bexpr = new bool_expression(0, e);
      (yyval._bool_expression) = bexpr;
      logic_expression_table1->push_back(bexpr);
    }    
  } else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 460:

/* Line 690 of lalr1.cc  */
#line 2995 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(5) - (1)].sval)!=NULL && (yysemantic_stack_[(5) - (3)].sval)!=NULL && (yysemantic_stack_[(5) - (5)]._expression)!=NULL) {
    int i = search_string_table((yysemantic_stack_[(5) - (1)].sval));
    int j = search_string_table((yysemantic_stack_[(5) - (3)].sval));
    variable *v;
    if(i>=0) {
      if(j>=0) {
	v = new variable((*string_table)[i], (*string_table)[j]);
	free((yysemantic_stack_[(5) - (3)].sval));
      } else {
	v = new variable((*string_table)[i], (yysemantic_stack_[(5) - (3)].sval));
	string_table->push_back((yysemantic_stack_[(5) - (3)].sval));
      }
      free((yysemantic_stack_[(5) - (1)].sval));
    } else {
      if(j>=0) {
	v = new variable((yysemantic_stack_[(5) - (1)].sval), (*string_table)[j]);
	free((yysemantic_stack_[(5) - (3)].sval));
      } else {
	v = new variable((yysemantic_stack_[(5) - (1)].sval), (yysemantic_stack_[(5) - (3)].sval));
	string_table->push_back((yysemantic_stack_[(5) - (3)].sval));
      }
      string_table->push_back((yysemantic_stack_[(5) - (1)].sval));
    }
    i = search_variable_table(v);
    if(i>=0) {
      delete v;
      v = (*variable_table)[i];
    } else {
      variable_table->push_back(v);
    }
    i = search_logic_expression_table1(v, (yysemantic_stack_[(5) - (5)]._expression));
    if(i>=0) {
      (yyval._bool_expression) = (*logic_expression_table1)[i];
      free((yysemantic_stack_[(5) - (5)]._expression));
    } else {
			logic_expression *e = new logic_expression(0, v, (yysemantic_stack_[(5) - (5)]._expression));
			bool_expression *bexpr = new bool_expression(0, e);
      (yyval._bool_expression) = bexpr;
      logic_expression_table1->push_back(bexpr);
    }    
  } else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 461:

/* Line 690 of lalr1.cc  */
#line 3039 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (1)].sval));
  USE((yysemantic_stack_[(5) - (3)].sval));
  USE((yysemantic_stack_[(5) - (5)]._expression));
 }
    break;

  case 462:

/* Line 690 of lalr1.cc  */
#line 3046 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (1)].sval));
  USE((yysemantic_stack_[(5) - (3)].sval));
  USE((yysemantic_stack_[(5) - (5)]._expression));
 }
    break;

  case 463:

/* Line 690 of lalr1.cc  */
#line 3053 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (1)].sval));
  USE((yysemantic_stack_[(5) - (3)].sval));
  USE((yysemantic_stack_[(5) - (5)]._expression));
 }
    break;

  case 464:

/* Line 690 of lalr1.cc  */
#line 3060 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(7) - (3)].sval)!=NULL && (yysemantic_stack_[(7) - (7)].sval)!=NULL) {
    int j = search_string_table((yysemantic_stack_[(7) - (3)].sval));
    variable *v;
    if(j>=0) {
      v = new variable((*string_table)[0], (*string_table)[j]);
      free((yysemantic_stack_[(7) - (3)].sval));
    } else {
      v = new variable((*string_table)[0], (yysemantic_stack_[(7) - (3)].sval));
      string_table->push_back((yysemantic_stack_[(7) - (3)].sval));
    }
    int i = search_variable_table(v);
    if(i>=0) {
      delete v;
      v = (*variable_table)[i];
    } else {
      variable_table->push_back(v);
    }

    j = search_string_table((yysemantic_stack_[(7) - (7)].sval));
    variable *v1;
    if(j>=0) {
      v1 = new variable((*string_table)[0], (*string_table)[j]);
      free((yysemantic_stack_[(7) - (7)].sval));
    } else {
      v1 = new variable((*string_table)[0], (yysemantic_stack_[(7) - (7)].sval));
      string_table->push_back((yysemantic_stack_[(7) - (7)].sval));
    }
    i = search_variable_table(v1);
    if(i>=0) {
      delete v1;
      v1 = (*variable_table)[i];
    } else {
      variable_table->push_back(v1);
    }

    i = search_logic_expression_table1(v, v1);
    if(i>=0) {
      (yyval._bool_expression) = (*logic_expression_table1)[i];
    } else {
			logic_expression *e = new logic_expression(0, v, v1);
			bool_expression *bexpr = new bool_expression(0, e);
      (yyval._bool_expression) = bexpr;
      logic_expression_table1->push_back(bexpr);
    }    
  } else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 465:

/* Line 690 of lalr1.cc  */
#line 3108 "parser/nssis_new.yy"
    {	
  if((yysemantic_stack_[(5) - (3)].sval)!=NULL && (yysemantic_stack_[(5) - (5)]._expression)!=NULL) {
    int j = search_string_table((yysemantic_stack_[(5) - (3)].sval));
    variable *v;
    if(j>=0) {
      v = new variable((*string_table)[0], (*string_table)[j]);
      free((yysemantic_stack_[(5) - (3)].sval));
    } else {
      v = new variable((*string_table)[0], (yysemantic_stack_[(5) - (3)].sval));
      string_table->push_back((yysemantic_stack_[(5) - (3)].sval));
    }
    j = search_variable_table(v);
    if(j>=0) {
      delete v;
      v = (*variable_table)[j];
    } else {
      variable_table->push_back(v);
    }
    j = search_logic_expression_table1(v, (yysemantic_stack_[(5) - (5)]._expression));
    if(j>=0) {
      (yyval._bool_expression) = (*logic_expression_table1)[j];
      free((yysemantic_stack_[(5) - (5)]._expression));
    } else {
			logic_expression *e = new logic_expression(0, v, (yysemantic_stack_[(5) - (5)]._expression));
			bool_expression *bexpr = new bool_expression(0, e);
      (yyval._bool_expression) = bexpr;
      logic_expression_table1->push_back(bexpr);
    }    
  } else
    (yyval._bool_expression) = NULL;
 }
    break;

  case 466:

/* Line 690 of lalr1.cc  */
#line 3139 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (3)].sval));
  USE((yysemantic_stack_[(5) - (5)]._expression));
 }
    break;

  case 467:

/* Line 690 of lalr1.cc  */
#line 3145 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (3)].sval));
  USE((yysemantic_stack_[(5) - (5)]._expression));
 }
    break;

  case 468:

/* Line 690 of lalr1.cc  */
#line 3151 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (3)].sval));
  USE((yysemantic_stack_[(5) - (5)]._expression));
 }
    break;

  case 469:

/* Line 690 of lalr1.cc  */
#line 3157 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(4) - (2)].sval));
  USE((yysemantic_stack_[(4) - (4)]._expression));
 }
    break;

  case 470:

/* Line 690 of lalr1.cc  */
#line 3163 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (3)].sval));
  USE((yysemantic_stack_[(5) - (5)]._expression));
 }
    break;

  case 471:

/* Line 690 of lalr1.cc  */
#line 3169 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(4) - (2)].sval));
  USE((yysemantic_stack_[(4) - (4)]._expression));
 }
    break;

  case 472:

/* Line 690 of lalr1.cc  */
#line 3175 "parser/nssis_new.yy"
    {
  (yyval._bool_expression) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 473:

/* Line 690 of lalr1.cc  */
#line 3182 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 474:

/* Line 690 of lalr1.cc  */
#line 3185 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 475:

/* Line 690 of lalr1.cc  */
#line 3189 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 476:

/* Line 690 of lalr1.cc  */
#line 3192 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 477:

/* Line 690 of lalr1.cc  */
#line 3196 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 478:

/* Line 690 of lalr1.cc  */
#line 3200 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
  }
    break;

  case 481:

/* Line 690 of lalr1.cc  */
#line 3206 "parser/nssis_new.yy"
    {
  driver.syntax_error = true;
  }
    break;

  case 482:

/* Line 690 of lalr1.cc  */
#line 3210 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 483:

/* Line 690 of lalr1.cc  */
#line 3213 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 484:

/* Line 690 of lalr1.cc  */
#line 3217 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 485:

/* Line 690 of lalr1.cc  */
#line 3221 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
  }
    break;

  case 486:

/* Line 690 of lalr1.cc  */
#line 3225 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 487:

/* Line 690 of lalr1.cc  */
#line 3228 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 488:

/* Line 690 of lalr1.cc  */
#line 3232 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 489:

/* Line 690 of lalr1.cc  */
#line 3236 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
  }
    break;

  case 490:

/* Line 690 of lalr1.cc  */
#line 3240 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(4) - (1)].sval)!=NULL && (yysemantic_stack_[(4) - (2)].ival)==1 && (yysemantic_stack_[(4) - (3)].set_string)!=NULL && (yysemantic_stack_[(4) - (4)].ival)==1) {
    (*is_groups)[*(yysemantic_stack_[(4) - (1)].sval)] = *(yysemantic_stack_[(4) - (3)].set_string);
    free((yysemantic_stack_[(4) - (1)].sval));
  }
 }
    break;

  case 491:

/* Line 690 of lalr1.cc  */
#line 3246 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(5) - (2)].sval)!=NULL && (yysemantic_stack_[(5) - (3)].ival)==1 && (yysemantic_stack_[(5) - (4)].set_string)!=NULL && (yysemantic_stack_[(5) - (5)].ival)==1) {
    if(is_groups->find(*(yysemantic_stack_[(5) - (2)].sval)) != is_groups->end() && options["quiet"] == 0)
      cout << "warning: group " << *(yysemantic_stack_[(5) - (2)].sval) << " already exists." << endl; 
    (*is_groups)[*(yysemantic_stack_[(5) - (2)].sval)] = *(yysemantic_stack_[(5) - (4)].set_string);
    free((yysemantic_stack_[(5) - (2)].sval));
  }
 }
    break;

  case 492:

/* Line 690 of lalr1.cc  */
#line 3254 "parser/nssis_new.yy"
    {
  driver.syntax_error = true;
  }
    break;

  case 493:

/* Line 690 of lalr1.cc  */
#line 3258 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(1) - (1)].sval)!=NULL) {
    (yyval.set_string) = new set<string>;
    (yyval.set_string)->insert(*(yysemantic_stack_[(1) - (1)].sval));
  } else
    (yyval.set_string) = NULL;
 }
    break;

  case 494:

/* Line 690 of lalr1.cc  */
#line 3265 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].set_string)!=NULL && (yysemantic_stack_[(3) - (3)].sval)!=NULL) {
    pair<set<string>::iterator, bool> ret = (yysemantic_stack_[(3) - (1)].set_string)->insert(*(yysemantic_stack_[(3) - (3)].sval));
    if(!ret.second && options["quiet"] == 0)
      cout << "warning: agent " << *(yysemantic_stack_[(3) - (3)].sval) << " in group definition is redundant." << endl;
    (yyval.set_string) = (yysemantic_stack_[(3) - (1)].set_string);
  } else
    (yyval.set_string) = NULL;
 }
    break;

  case 495:

/* Line 690 of lalr1.cc  */
#line 3274 "parser/nssis_new.yy"
    {
  (yyval.set_string) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)].set_string));USE((yysemantic_stack_[(3) - (3)].sval));
 }
    break;

  case 496:

/* Line 690 of lalr1.cc  */
#line 3279 "parser/nssis_new.yy"
    {
  (yyval.set_string) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 497:

/* Line 690 of lalr1.cc  */
#line 3283 "parser/nssis_new.yy"
    {
  (yyval.sval) = (*string_table)[0];
 }
    break;

  case 498:

/* Line 690 of lalr1.cc  */
#line 3286 "parser/nssis_new.yy"
    {
    int i = search_string_table((yysemantic_stack_[(1) - (1)].sval));
    if(i>=0) {
      (yyval.sval) = (*string_table)[i];
      free((yysemantic_stack_[(1) - (1)].sval));
    } else {
      (yyval.sval) = (yysemantic_stack_[(1) - (1)].sval);
      string_table->push_back((yysemantic_stack_[(1) - (1)].sval));
    }
  }
    break;

  case 499:

/* Line 690 of lalr1.cc  */
#line 3296 "parser/nssis_new.yy"
    {
  (yyval.sval) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 500:

/* Line 690 of lalr1.cc  */
#line 3303 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 501:

/* Line 690 of lalr1.cc  */
#line 3306 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 502:

/* Line 690 of lalr1.cc  */
#line 3310 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 503:

/* Line 690 of lalr1.cc  */
#line 3313 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 504:

/* Line 690 of lalr1.cc  */
#line 3317 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 505:

/* Line 690 of lalr1.cc  */
#line 3321 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
  }
    break;

  case 508:

/* Line 690 of lalr1.cc  */
#line 3328 "parser/nssis_new.yy"
    { 
  if((yysemantic_stack_[(2) - (1)]._fairness_expression)!=NULL)
    is_fairness->push_back((yysemantic_stack_[(2) - (1)]._fairness_expression));
 }
    break;

  case 509:

/* Line 690 of lalr1.cc  */
#line 3332 "parser/nssis_new.yy"
    {
  driver.syntax_error = true;
  USE((yysemantic_stack_[(2) - (1)]._fairness_expression));
 }
    break;

  case 510:

/* Line 690 of lalr1.cc  */
#line 3336 "parser/nssis_new.yy"
    { 
  if((yysemantic_stack_[(3) - (2)]._fairness_expression)!=NULL)
    is_fairness->push_back((yysemantic_stack_[(3) - (2)]._fairness_expression)); 
 }
    break;

  case 511:

/* Line 690 of lalr1.cc  */
#line 3340 "parser/nssis_new.yy"
    {
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._fairness_expression));
 }
    break;

  case 512:

/* Line 690 of lalr1.cc  */
#line 3344 "parser/nssis_new.yy"
    {
  driver.syntax_error = true;
  }
    break;

  case 513:

/* Line 690 of lalr1.cc  */
#line 3348 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(5) - (2)]._fairness_expression)!=NULL && (yysemantic_stack_[(5) - (4)]._fairness_expression)!=NULL)
    (yyval.dual_fairness_expression) = new pair<fairness_expression *, fairness_expression *>((yysemantic_stack_[(5) - (2)]._fairness_expression), (yysemantic_stack_[(5) - (4)]._fairness_expression));
  else
    (yyval.dual_fairness_expression) = NULL;
 }
    break;

  case 514:

/* Line 690 of lalr1.cc  */
#line 3354 "parser/nssis_new.yy"
    {
  (yyval.dual_fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)]._fairness_expression));USE((yysemantic_stack_[(5) - (4)]._fairness_expression));
 }
    break;

  case 515:

/* Line 690 of lalr1.cc  */
#line 3359 "parser/nssis_new.yy"
    {
  (yyval.dual_fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)]._fairness_expression));USE((yysemantic_stack_[(5) - (4)]._fairness_expression));
 }
    break;

  case 516:

/* Line 690 of lalr1.cc  */
#line 3364 "parser/nssis_new.yy"
    {
  (yyval.dual_fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)]._fairness_expression));USE((yysemantic_stack_[(5) - (4)]._fairness_expression));
 }
    break;

  case 517:

/* Line 690 of lalr1.cc  */
#line 3369 "parser/nssis_new.yy"
    {
  (yyval.dual_fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)]._fairness_expression));USE((yysemantic_stack_[(5) - (4)]._fairness_expression));
 }
    break;

  case 518:

/* Line 690 of lalr1.cc  */
#line 3374 "parser/nssis_new.yy"
    {
  (yyval.dual_fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)]._fairness_expression));USE((yysemantic_stack_[(5) - (4)]._fairness_expression));
 }
    break;

  case 519:

/* Line 690 of lalr1.cc  */
#line 3379 "parser/nssis_new.yy"
    {
  (yyval.dual_fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)]._fairness_expression));USE((yysemantic_stack_[(5) - (4)]._fairness_expression));
 }
    break;

  case 520:

/* Line 690 of lalr1.cc  */
#line 3384 "parser/nssis_new.yy"
    {
  (yyval.dual_fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)]._fairness_expression));USE((yysemantic_stack_[(5) - (4)]._fairness_expression));
 }
    break;

  case 521:

/* Line 690 of lalr1.cc  */
#line 3389 "parser/nssis_new.yy"
    {
    if((yysemantic_stack_[(5) - (2)].sval)!=NULL && (yysemantic_stack_[(5) - (4)]._fairness_expression)!=NULL) {
      int i = search_string_table((yysemantic_stack_[(5) - (2)].sval));
      if(i>=0) {
	(yyval.ID_fairness_expression) = new pair<string *, fairness_expression *>((*string_table)[i], (yysemantic_stack_[(5) - (4)]._fairness_expression));
	free((yysemantic_stack_[(5) - (2)].sval));
      } else {
	(yyval.ID_fairness_expression) = new pair<string *, fairness_expression *>((yysemantic_stack_[(5) - (2)].sval), (yysemantic_stack_[(5) - (4)]._fairness_expression));
	string_table->push_back((yysemantic_stack_[(5) - (2)].sval));
      }
    } else
      (yyval.ID_fairness_expression) = NULL;
 }
    break;

  case 522:

/* Line 690 of lalr1.cc  */
#line 3402 "parser/nssis_new.yy"
    {
  (yyval.ID_fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._fairness_expression));
 }
    break;

  case 523:

/* Line 690 of lalr1.cc  */
#line 3408 "parser/nssis_new.yy"
    {
  (yyval.ID_fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._fairness_expression));
 }
    break;

  case 524:

/* Line 690 of lalr1.cc  */
#line 3414 "parser/nssis_new.yy"
    {
  (yyval.ID_fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._fairness_expression));
 }
    break;

  case 525:

/* Line 690 of lalr1.cc  */
#line 3420 "parser/nssis_new.yy"
    {
  (yyval.ID_fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._fairness_expression));
 }
    break;

  case 526:

/* Line 690 of lalr1.cc  */
#line 3426 "parser/nssis_new.yy"
    {
  (yyval.ID_fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._fairness_expression));
 }
    break;

  case 527:

/* Line 690 of lalr1.cc  */
#line 3432 "parser/nssis_new.yy"
    {
  (yyval.ID_fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._fairness_expression));
 }
    break;

  case 528:

/* Line 690 of lalr1.cc  */
#line 3438 "parser/nssis_new.yy"
    {
  (yyval.ID_fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._fairness_expression));
 }
    break;

  case 529:

/* Line 690 of lalr1.cc  */
#line 3444 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(5) - (4)]._fairness_expression)!=NULL)
    (yyval.ID_fairness_expression) = new pair<string *, fairness_expression *>((*string_table)[0], (yysemantic_stack_[(5) - (4)]._fairness_expression));
  else
    (yyval.ID_fairness_expression) = NULL;
 }
    break;

  case 530:

/* Line 690 of lalr1.cc  */
#line 3450 "parser/nssis_new.yy"
    {
  (yyval.ID_fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (4)]._fairness_expression));
 }
    break;

  case 531:

/* Line 690 of lalr1.cc  */
#line 3455 "parser/nssis_new.yy"
    {
  (yyval.ID_fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (4)]._fairness_expression));
 }
    break;

  case 532:

/* Line 690 of lalr1.cc  */
#line 3460 "parser/nssis_new.yy"
    {
  (yyval.ID_fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (4)]._fairness_expression));
 }
    break;

  case 533:

/* Line 690 of lalr1.cc  */
#line 3465 "parser/nssis_new.yy"
    {
  (yyval.ID_fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (4)]._fairness_expression));
 }
    break;

  case 534:

/* Line 690 of lalr1.cc  */
#line 3470 "parser/nssis_new.yy"
    {
  (yyval.ID_fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (4)]._fairness_expression));
 }
    break;

  case 535:

/* Line 690 of lalr1.cc  */
#line 3475 "parser/nssis_new.yy"
    {
  (yyval.ID_fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (4)]._fairness_expression));
 }
    break;

  case 536:

/* Line 690 of lalr1.cc  */
#line 3480 "parser/nssis_new.yy"
    {
  (yyval.ID_fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (4)]._fairness_expression));
 }
    break;

  case 537:

/* Line 690 of lalr1.cc  */
#line 3485 "parser/nssis_new.yy"
    {
    if((yysemantic_stack_[(5) - (2)].sval)!=NULL && (yysemantic_stack_[(5) - (4)]._fairness_expression)!=NULL) {
      int i = search_string_table((yysemantic_stack_[(5) - (2)].sval));
      if(i>=0) {
	(yyval.ID_fairness_expression) = new pair<string *, fairness_expression *>((*string_table)[i], (yysemantic_stack_[(5) - (4)]._fairness_expression));
	free((yysemantic_stack_[(5) - (2)].sval));
      } else {
	(yyval.ID_fairness_expression) = new pair<string *, fairness_expression *>((yysemantic_stack_[(5) - (2)].sval), (yysemantic_stack_[(5) - (4)]._fairness_expression));
	string_table->push_back((yysemantic_stack_[(5) - (2)].sval));
      }
    } else
      (yyval.ID_fairness_expression) = NULL;
 }
    break;

  case 538:

/* Line 690 of lalr1.cc  */
#line 3498 "parser/nssis_new.yy"
    {
  (yyval.ID_fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._fairness_expression));
 }
    break;

  case 539:

/* Line 690 of lalr1.cc  */
#line 3504 "parser/nssis_new.yy"
    {
  (yyval.ID_fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._fairness_expression));
 }
    break;

  case 540:

/* Line 690 of lalr1.cc  */
#line 3510 "parser/nssis_new.yy"
    {
  (yyval.ID_fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._fairness_expression));
 }
    break;

  case 541:

/* Line 690 of lalr1.cc  */
#line 3516 "parser/nssis_new.yy"
    {
  (yyval.ID_fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._fairness_expression));
 }
    break;

  case 542:

/* Line 690 of lalr1.cc  */
#line 3522 "parser/nssis_new.yy"
    {
  (yyval.ID_fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._fairness_expression));
 }
    break;

  case 543:

/* Line 690 of lalr1.cc  */
#line 3528 "parser/nssis_new.yy"
    {
  (yyval.ID_fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._fairness_expression));
 }
    break;

  case 544:

/* Line 690 of lalr1.cc  */
#line 3534 "parser/nssis_new.yy"
    {
  (yyval.ID_fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._fairness_expression));
 }
    break;

  case 545:

/* Line 690 of lalr1.cc  */
#line 3541 "parser/nssis_new.yy"
    { 
  (yyval._fairness_expression) = (yysemantic_stack_[(3) - (2)]._fairness_expression); 
 }
    break;

  case 546:

/* Line 690 of lalr1.cc  */
#line 3544 "parser/nssis_new.yy"
    { 
  (yyval._fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._fairness_expression));
 }
    break;

  case 547:

/* Line 690 of lalr1.cc  */
#line 3549 "parser/nssis_new.yy"
    { 
  (yyval._fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._fairness_expression));
 }
    break;

  case 548:

/* Line 690 of lalr1.cc  */
#line 3554 "parser/nssis_new.yy"
    { 
  (yyval._fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._fairness_expression));
 }
    break;

  case 549:

/* Line 690 of lalr1.cc  */
#line 3559 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._fairness_expression)!=NULL && (yysemantic_stack_[(3) - (3)]._fairness_expression)!=NULL)
    (yyval._fairness_expression) = new fairness_expression(1, (yysemantic_stack_[(3) - (1)]._fairness_expression), (yysemantic_stack_[(3) - (3)]._fairness_expression));
  else
    (yyval._fairness_expression) = NULL;
 }
    break;

  case 550:

/* Line 690 of lalr1.cc  */
#line 3565 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._fairness_expression)!=NULL && (yysemantic_stack_[(3) - (3)]._fairness_expression)!=NULL)
    (yyval._fairness_expression) = new fairness_expression(2, (yysemantic_stack_[(3) - (1)]._fairness_expression), (yysemantic_stack_[(3) - (3)]._fairness_expression));
  else
    (yyval._fairness_expression) = NULL;
 }
    break;

  case 551:

/* Line 690 of lalr1.cc  */
#line 3571 "parser/nssis_new.yy"
    {
  (yyval._fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)]._fairness_expression));USE((yysemantic_stack_[(3) - (3)]._fairness_expression));
 }
    break;

  case 552:

/* Line 690 of lalr1.cc  */
#line 3576 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)]._fairness_expression)!=NULL)
    (yyval._fairness_expression) = new fairness_expression(3, (yysemantic_stack_[(2) - (2)]._fairness_expression));
  else
    (yyval._fairness_expression) = NULL;
 }
    break;

  case 553:

/* Line 690 of lalr1.cc  */
#line 3582 "parser/nssis_new.yy"
    {
  (yyval._fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(2) - (2)]._fairness_expression));
 }
    break;

  case 554:

/* Line 690 of lalr1.cc  */
#line 3587 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._fairness_expression)!=NULL && (yysemantic_stack_[(3) - (3)]._fairness_expression)!=NULL)
    (yyval._fairness_expression) = new fairness_expression(4, (yysemantic_stack_[(3) - (1)]._fairness_expression), (yysemantic_stack_[(3) - (3)]._fairness_expression));
  else
    (yyval._fairness_expression) = NULL;
 }
    break;

  case 555:

/* Line 690 of lalr1.cc  */
#line 3593 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)]._fairness_expression)!=NULL)
    (yyval._fairness_expression) = new fairness_expression(10, (yysemantic_stack_[(2) - (2)]._fairness_expression));
  else
    (yyval._fairness_expression) = NULL;
 }
    break;

  case 556:

/* Line 690 of lalr1.cc  */
#line 3599 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)]._fairness_expression)!=NULL)
    (yyval._fairness_expression) = new fairness_expression(11, (yysemantic_stack_[(2) - (2)]._fairness_expression));
  else
    (yyval._fairness_expression) = NULL;
  }
    break;

  case 557:

/* Line 690 of lalr1.cc  */
#line 3605 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)]._fairness_expression)!=NULL)
    (yyval._fairness_expression) = new fairness_expression(12, (yysemantic_stack_[(2) - (2)]._fairness_expression));
  else
    (yyval._fairness_expression) = NULL;
 }
    break;

  case 558:

/* Line 690 of lalr1.cc  */
#line 3611 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)]._fairness_expression)!=NULL)
    (yyval._fairness_expression) = new fairness_expression(13, (yysemantic_stack_[(2) - (2)]._fairness_expression));
  else
    (yyval._fairness_expression) = NULL;
 }
    break;

  case 559:

/* Line 690 of lalr1.cc  */
#line 3617 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)]._fairness_expression)!=NULL)
    (yyval._fairness_expression) = new fairness_expression(14, (yysemantic_stack_[(2) - (2)]._fairness_expression));
  else
    (yyval._fairness_expression) = NULL;
 }
    break;

  case 560:

/* Line 690 of lalr1.cc  */
#line 3623 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)]._fairness_expression)!=NULL)
    (yyval._fairness_expression) = new fairness_expression(15, (yysemantic_stack_[(2) - (2)]._fairness_expression));
  else
    (yyval._fairness_expression) = NULL;
 }
    break;

  case 561:

/* Line 690 of lalr1.cc  */
#line 3629 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)].dual_fairness_expression)!=NULL) {
    (yyval._fairness_expression) = new fairness_expression(16, (yysemantic_stack_[(2) - (2)].dual_fairness_expression)->first, (yysemantic_stack_[(2) - (2)].dual_fairness_expression)->second);
    free((yysemantic_stack_[(2) - (2)].dual_fairness_expression));
  }
  else
    (yyval._fairness_expression) = NULL;
 }
    break;

  case 562:

/* Line 690 of lalr1.cc  */
#line 3637 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)].dual_fairness_expression)!=NULL) {
    (yyval._fairness_expression) = new fairness_expression(17, (yysemantic_stack_[(2) - (2)].dual_fairness_expression)->first, (yysemantic_stack_[(2) - (2)].dual_fairness_expression)->second);
    free((yysemantic_stack_[(2) - (2)].dual_fairness_expression));
  }
  else
    (yyval._fairness_expression) = NULL;
 }
    break;

  case 563:

/* Line 690 of lalr1.cc  */
#line 3645 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)].ID_fairness_expression)!=NULL) {
    atomic_proposition *ap = new atomic_proposition((yysemantic_stack_[(2) - (2)].ID_fairness_expression)->first);
    fairness_expression *a = new fairness_expression(ap);
    (yyval._fairness_expression) = new fairness_expression(30, a, (yysemantic_stack_[(2) - (2)].ID_fairness_expression)->second);
    free((yysemantic_stack_[(2) - (2)].ID_fairness_expression));
  } else
    (yyval._fairness_expression) = NULL;
 }
    break;

  case 564:

/* Line 690 of lalr1.cc  */
#line 3654 "parser/nssis_new.yy"
    {
  // Knowledge in a group (everybody knows)
  if((yysemantic_stack_[(2) - (2)].ID_fairness_expression)!=NULL) {
    atomic_proposition *ap = new atomic_proposition((yysemantic_stack_[(2) - (2)].ID_fairness_expression)->first);
    fairness_expression *a = new fairness_expression(ap);
    (yyval._fairness_expression) = new fairness_expression(31, a, (yysemantic_stack_[(2) - (2)].ID_fairness_expression)->second);
    free((yysemantic_stack_[(2) - (2)].ID_fairness_expression));
  } else
    (yyval._fairness_expression) = NULL;
 }
    break;

  case 565:

/* Line 690 of lalr1.cc  */
#line 3664 "parser/nssis_new.yy"
    {
  // Common knowledge in a group
  if((yysemantic_stack_[(2) - (2)].ID_fairness_expression)!=NULL) {
    atomic_proposition *ap = new atomic_proposition((yysemantic_stack_[(2) - (2)].ID_fairness_expression)->first);
    fairness_expression *a = new fairness_expression(ap);
    (yyval._fairness_expression) = new fairness_expression(32, a, (yysemantic_stack_[(2) - (2)].ID_fairness_expression)->second);
    free((yysemantic_stack_[(2) - (2)].ID_fairness_expression));
  } else
    (yyval._fairness_expression) = NULL;
 }
    break;

  case 566:

/* Line 690 of lalr1.cc  */
#line 3674 "parser/nssis_new.yy"
    {
  // deontic operator
  if((yysemantic_stack_[(2) - (2)].ID_fairness_expression)!=NULL) {
    atomic_proposition *ap = new atomic_proposition((yysemantic_stack_[(2) - (2)].ID_fairness_expression)->first);
    fairness_expression *a = new fairness_expression(ap);
    (yyval._fairness_expression) = new fairness_expression(40, a, (yysemantic_stack_[(2) - (2)].ID_fairness_expression)->second);
    free((yysemantic_stack_[(2) - (2)].ID_fairness_expression));
  } else
    (yyval._fairness_expression) = NULL;
 }
    break;

  case 567:

/* Line 690 of lalr1.cc  */
#line 3684 "parser/nssis_new.yy"
    {
  // Distributed knowledge in a group
  if((yysemantic_stack_[(2) - (2)].ID_fairness_expression)!=NULL) {
    atomic_proposition *ap = new atomic_proposition((yysemantic_stack_[(2) - (2)].ID_fairness_expression)->first);
    fairness_expression *a = new fairness_expression(ap);
    (yyval._fairness_expression) = new fairness_expression(42, a, (yysemantic_stack_[(2) - (2)].ID_fairness_expression)->second);
    free((yysemantic_stack_[(2) - (2)].ID_fairness_expression));
  } else
    (yyval._fairness_expression) = NULL;
 }
    break;

  case 568:

/* Line 690 of lalr1.cc  */
#line 3694 "parser/nssis_new.yy"
    { 
  (yyval._fairness_expression) = NULL;
  if((yysemantic_stack_[(2) - (2)].ID_fairness_expression) != NULL)
    free((yysemantic_stack_[(2) - (2)].ID_fairness_expression));
  driver.syntax_error = true;
 }
    break;

  case 569:

/* Line 690 of lalr1.cc  */
#line 3700 "parser/nssis_new.yy"
    { 
  (yyval._fairness_expression) = NULL;
  if((yysemantic_stack_[(2) - (2)].ID_fairness_expression) != NULL)
    free((yysemantic_stack_[(2) - (2)].ID_fairness_expression));
  driver.syntax_error = true;
 }
    break;

  case 570:

/* Line 690 of lalr1.cc  */
#line 3706 "parser/nssis_new.yy"
    {	
  if((yysemantic_stack_[(1) - (1)].sval)!=NULL) {
    int i = search_string_table((yysemantic_stack_[(1) - (1)].sval));
    atomic_proposition *ap;
    if(i>=0) {
      ap = new atomic_proposition((*string_table)[i]);
      free((yysemantic_stack_[(1) - (1)].sval));
    } else {
      ap = new atomic_proposition((yysemantic_stack_[(1) - (1)].sval));
      string_table->push_back((yysemantic_stack_[(1) - (1)].sval));
    }
    (yyval._fairness_expression) = new fairness_expression(ap);
  } else
    (yyval._fairness_expression) = NULL;
  }
    break;

  case 571:

/* Line 690 of lalr1.cc  */
#line 3721 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].sval)!=NULL) {
    string *newname = new string(*(yysemantic_stack_[(3) - (1)].sval) + ".GreenStates");
    atomic_proposition *ap;
    int i = search_string_table(newname);
    if(i>=0) {
      ap = new atomic_proposition((*string_table)[i]);
      free(newname);
    } else {
      ap = new atomic_proposition(newname);
      string_table->push_back(newname);
    }
    free((yysemantic_stack_[(3) - (1)].sval));
    (yyval._fairness_expression) = new fairness_expression(ap);
  } else
    (yyval._fairness_expression) = NULL;
 }
    break;

  case 572:

/* Line 690 of lalr1.cc  */
#line 3738 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].sval)!=NULL) {
    string *newname = new string(*(yysemantic_stack_[(3) - (1)].sval) + ".RedStates");
    atomic_proposition *ap;
    int i = search_string_table(newname);
    if(i>=0) {
      ap = new atomic_proposition((*string_table)[i]);
      free(newname);
    } else {
      ap = new atomic_proposition(newname);
      string_table->push_back(newname);
    }
    free((yysemantic_stack_[(3) - (1)].sval));
    (yyval._fairness_expression) = new fairness_expression(ap);
  } else
    (yyval._fairness_expression) = NULL;
 }
    break;

  case 573:

/* Line 690 of lalr1.cc  */
#line 3755 "parser/nssis_new.yy"
    {
    string *newname = new string("Environment.GreenStates");
    atomic_proposition *ap;
    int i = search_string_table(newname);
    if(i>=0) {
      ap = new atomic_proposition((*string_table)[i]);
      free(newname);
    } else {
      ap = new atomic_proposition(newname);
      string_table->push_back(newname);
    }
    (yyval._fairness_expression) = new fairness_expression(ap);
 }
    break;

  case 574:

/* Line 690 of lalr1.cc  */
#line 3768 "parser/nssis_new.yy"
    {
  string *newname = new string("Environment.RedStates");
  atomic_proposition *ap;
  int i = search_string_table(newname);
  if(i>=0) {
    ap = new atomic_proposition((*string_table)[i]);
    free(newname);
  } else {
    ap = new atomic_proposition(newname);
    string_table->push_back(newname);
  }
  (yyval._fairness_expression) = new fairness_expression(ap);
 }
    break;

  case 575:

/* Line 690 of lalr1.cc  */
#line 3781 "parser/nssis_new.yy"
    {
  (yyval._fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)].sval));
 }
    break;

  case 576:

/* Line 690 of lalr1.cc  */
#line 3786 "parser/nssis_new.yy"
    {
  (yyval._fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)].sval));
 }
    break;

  case 577:

/* Line 690 of lalr1.cc  */
#line 3791 "parser/nssis_new.yy"
    {
  (yyval._fairness_expression) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)].sval));
 }
    break;

  case 578:

/* Line 690 of lalr1.cc  */
#line 3796 "parser/nssis_new.yy"
    {
  (yyval._fairness_expression) = NULL;
  driver.syntax_error = true;
  }
    break;

  case 579:

/* Line 690 of lalr1.cc  */
#line 3803 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 580:

/* Line 690 of lalr1.cc  */
#line 3806 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 581:

/* Line 690 of lalr1.cc  */
#line 3810 "parser/nssis_new.yy"
    {
  (yyval.ival) = 1;
 }
    break;

  case 582:

/* Line 690 of lalr1.cc  */
#line 3813 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 583:

/* Line 690 of lalr1.cc  */
#line 3817 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
 }
    break;

  case 584:

/* Line 690 of lalr1.cc  */
#line 3821 "parser/nssis_new.yy"
    {
  (yyval.ival) = 0;
  driver.syntax_error = true;
  }
    break;

  case 586:

/* Line 690 of lalr1.cc  */
#line 3827 "parser/nssis_new.yy"
    { 
  if((yysemantic_stack_[(2) - (1)]._modal_formula)!=NULL) {
    is_formulae->push_back(*(yysemantic_stack_[(2) - (1)]._modal_formula));
  }
 }
    break;

  case 587:

/* Line 690 of lalr1.cc  */
#line 3832 "parser/nssis_new.yy"
    {
  driver.syntax_error = true;
  USE((yysemantic_stack_[(2) - (1)]._modal_formula));
 }
    break;

  case 588:

/* Line 690 of lalr1.cc  */
#line 3836 "parser/nssis_new.yy"
    { 
  if((yysemantic_stack_[(3) - (2)]._modal_formula)!=NULL) {
    is_formulae->push_back(*(yysemantic_stack_[(3) - (2)]._modal_formula)); 
  }
 }
    break;

  case 589:

/* Line 690 of lalr1.cc  */
#line 3841 "parser/nssis_new.yy"
    {
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._modal_formula));
 }
    break;

  case 590:

/* Line 690 of lalr1.cc  */
#line 3845 "parser/nssis_new.yy"
    {
  driver.syntax_error = true;
  }
    break;

  case 591:

/* Line 690 of lalr1.cc  */
#line 3849 "parser/nssis_new.yy"
    {
    int i = search_string_table((yysemantic_stack_[(3) - (2)].sval));
    if(i>=0) {
      (yyval.sval) = (*string_table)[i];
      free((yysemantic_stack_[(3) - (2)].sval));
    } else {
      (yyval.sval) = (yysemantic_stack_[(3) - (2)].sval);
      string_table->push_back((yysemantic_stack_[(3) - (2)].sval));
    }
 }
    break;

  case 592:

/* Line 690 of lalr1.cc  */
#line 3859 "parser/nssis_new.yy"
    {
  (yyval.sval) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)].sval));
 }
    break;

  case 593:

/* Line 690 of lalr1.cc  */
#line 3864 "parser/nssis_new.yy"
    {
  (yyval.sval) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)].sval));
 }
    break;

  case 594:

/* Line 690 of lalr1.cc  */
#line 3869 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(5) - (2)]._modal_formula)!=NULL && (yysemantic_stack_[(5) - (4)]._modal_formula)!=NULL)
    (yyval.dual_modal_formula) = new pair<modal_formula *, modal_formula *>((yysemantic_stack_[(5) - (2)]._modal_formula), (yysemantic_stack_[(5) - (4)]._modal_formula));
  else
    (yyval.dual_modal_formula) = NULL;
 }
    break;

  case 595:

/* Line 690 of lalr1.cc  */
#line 3875 "parser/nssis_new.yy"
    {
  (yyval.dual_modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)]._modal_formula));USE((yysemantic_stack_[(5) - (4)]._modal_formula));
 }
    break;

  case 596:

/* Line 690 of lalr1.cc  */
#line 3880 "parser/nssis_new.yy"
    {
  (yyval.dual_modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)]._modal_formula));USE((yysemantic_stack_[(5) - (4)]._modal_formula));
 }
    break;

  case 597:

/* Line 690 of lalr1.cc  */
#line 3885 "parser/nssis_new.yy"
    {
  (yyval.dual_modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)]._modal_formula));USE((yysemantic_stack_[(5) - (4)]._modal_formula));
 }
    break;

  case 598:

/* Line 690 of lalr1.cc  */
#line 3890 "parser/nssis_new.yy"
    {
  (yyval.dual_modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)]._modal_formula));USE((yysemantic_stack_[(5) - (4)]._modal_formula));
 }
    break;

  case 599:

/* Line 690 of lalr1.cc  */
#line 3895 "parser/nssis_new.yy"
    {
  (yyval.dual_modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)]._modal_formula));USE((yysemantic_stack_[(5) - (4)]._modal_formula));
 }
    break;

  case 600:

/* Line 690 of lalr1.cc  */
#line 3900 "parser/nssis_new.yy"
    {
  (yyval.dual_modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)]._modal_formula));USE((yysemantic_stack_[(5) - (4)]._modal_formula));
 }
    break;

  case 601:

/* Line 690 of lalr1.cc  */
#line 3905 "parser/nssis_new.yy"
    {
  (yyval.dual_modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)]._modal_formula));USE((yysemantic_stack_[(5) - (4)]._modal_formula));
 }
    break;

  case 602:

/* Line 690 of lalr1.cc  */
#line 3910 "parser/nssis_new.yy"
    {
    if((yysemantic_stack_[(5) - (2)].sval)!=NULL && (yysemantic_stack_[(5) - (4)]._modal_formula)!=NULL) {
      int i = search_string_table((yysemantic_stack_[(5) - (2)].sval));
      if(i>=0) {
	(yyval.ID_modal_formula) = new pair<string *, modal_formula *>((*string_table)[i], (yysemantic_stack_[(5) - (4)]._modal_formula));
	free((yysemantic_stack_[(5) - (2)].sval));
      } else {
	(yyval.ID_modal_formula) = new pair<string *, modal_formula *>((yysemantic_stack_[(5) - (2)].sval), (yysemantic_stack_[(5) - (4)]._modal_formula));
	string_table->push_back((yysemantic_stack_[(5) - (2)].sval));
      }
    } else
    (yyval.ID_modal_formula) = NULL;
 }
    break;

  case 603:

/* Line 690 of lalr1.cc  */
#line 3923 "parser/nssis_new.yy"
    {
  (yyval.ID_modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._modal_formula));
 }
    break;

  case 604:

/* Line 690 of lalr1.cc  */
#line 3929 "parser/nssis_new.yy"
    {
  (yyval.ID_modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._modal_formula));
 }
    break;

  case 605:

/* Line 690 of lalr1.cc  */
#line 3935 "parser/nssis_new.yy"
    {
  (yyval.ID_modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._modal_formula));
 }
    break;

  case 606:

/* Line 690 of lalr1.cc  */
#line 3941 "parser/nssis_new.yy"
    {
  (yyval.ID_modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._modal_formula));
 }
    break;

  case 607:

/* Line 690 of lalr1.cc  */
#line 3947 "parser/nssis_new.yy"
    {
  (yyval.ID_modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._modal_formula));
 }
    break;

  case 608:

/* Line 690 of lalr1.cc  */
#line 3953 "parser/nssis_new.yy"
    {
  (yyval.ID_modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._modal_formula));
 }
    break;

  case 609:

/* Line 690 of lalr1.cc  */
#line 3959 "parser/nssis_new.yy"
    {
  (yyval.ID_modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._modal_formula));
 }
    break;

  case 610:

/* Line 690 of lalr1.cc  */
#line 3965 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(5) - (4)]._modal_formula)!=NULL)
    (yyval.ID_modal_formula) = new pair<string *, modal_formula *>((*string_table)[0], (yysemantic_stack_[(5) - (4)]._modal_formula));
  else
    (yyval.ID_modal_formula) = NULL;
 }
    break;

  case 611:

/* Line 690 of lalr1.cc  */
#line 3971 "parser/nssis_new.yy"
    {
  (yyval.ID_modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (4)]._modal_formula));
 }
    break;

  case 612:

/* Line 690 of lalr1.cc  */
#line 3976 "parser/nssis_new.yy"
    {
  (yyval.ID_modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (4)]._modal_formula));
 }
    break;

  case 613:

/* Line 690 of lalr1.cc  */
#line 3981 "parser/nssis_new.yy"
    {
  (yyval.ID_modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (4)]._modal_formula));
 }
    break;

  case 614:

/* Line 690 of lalr1.cc  */
#line 3986 "parser/nssis_new.yy"
    {
  (yyval.ID_modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (4)]._modal_formula));
 }
    break;

  case 615:

/* Line 690 of lalr1.cc  */
#line 3991 "parser/nssis_new.yy"
    {
  (yyval.ID_modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (4)]._modal_formula));
 }
    break;

  case 616:

/* Line 690 of lalr1.cc  */
#line 3996 "parser/nssis_new.yy"
    {
  (yyval.ID_modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (4)]._modal_formula));
 }
    break;

  case 617:

/* Line 690 of lalr1.cc  */
#line 4001 "parser/nssis_new.yy"
    {
  (yyval.ID_modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (4)]._modal_formula));
 }
    break;

  case 618:

/* Line 690 of lalr1.cc  */
#line 4006 "parser/nssis_new.yy"
    {
    if((yysemantic_stack_[(5) - (2)].sval)!=NULL && (yysemantic_stack_[(5) - (4)]._modal_formula)!=NULL) {
      int i = search_string_table((yysemantic_stack_[(5) - (2)].sval));
      if(i>=0) {
	(yyval.ID_modal_formula) = new pair<string *, modal_formula *>((*string_table)[i], (yysemantic_stack_[(5) - (4)]._modal_formula));
	free((yysemantic_stack_[(5) - (2)].sval));
      } else {
	(yyval.ID_modal_formula) = new pair<string *, modal_formula *>((yysemantic_stack_[(5) - (2)].sval), (yysemantic_stack_[(5) - (4)]._modal_formula));
	string_table->push_back((yysemantic_stack_[(5) - (2)].sval));
      }
    } else
      (yyval.ID_modal_formula) = NULL;
 }
    break;

  case 619:

/* Line 690 of lalr1.cc  */
#line 4019 "parser/nssis_new.yy"
    {
  (yyval.ID_modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._modal_formula));
 }
    break;

  case 620:

/* Line 690 of lalr1.cc  */
#line 4025 "parser/nssis_new.yy"
    {
  (yyval.ID_modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._modal_formula));
 }
    break;

  case 621:

/* Line 690 of lalr1.cc  */
#line 4031 "parser/nssis_new.yy"
    {
  (yyval.ID_modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._modal_formula));
 }
    break;

  case 622:

/* Line 690 of lalr1.cc  */
#line 4037 "parser/nssis_new.yy"
    {
  (yyval.ID_modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._modal_formula));
 }
    break;

  case 623:

/* Line 690 of lalr1.cc  */
#line 4043 "parser/nssis_new.yy"
    {
  (yyval.ID_modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._modal_formula));
 }
    break;

  case 624:

/* Line 690 of lalr1.cc  */
#line 4049 "parser/nssis_new.yy"
    {
  (yyval.ID_modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._modal_formula));
 }
    break;

  case 625:

/* Line 690 of lalr1.cc  */
#line 4055 "parser/nssis_new.yy"
    {
  (yyval.ID_modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(5) - (2)].sval));
  USE((yysemantic_stack_[(5) - (4)]._modal_formula));
 }
    break;

  case 626:

/* Line 690 of lalr1.cc  */
#line 4062 "parser/nssis_new.yy"
    { 
  (yyval._modal_formula) = (yysemantic_stack_[(3) - (2)]._modal_formula); 
 }
    break;

  case 627:

/* Line 690 of lalr1.cc  */
#line 4065 "parser/nssis_new.yy"
    { 
  (yyval._modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._modal_formula));
 }
    break;

  case 628:

/* Line 690 of lalr1.cc  */
#line 4070 "parser/nssis_new.yy"
    { 
  (yyval._modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._modal_formula));
 }
    break;

  case 629:

/* Line 690 of lalr1.cc  */
#line 4075 "parser/nssis_new.yy"
    { 
  (yyval._modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (2)]._modal_formula));
 }
    break;

  case 630:

/* Line 690 of lalr1.cc  */
#line 4080 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._modal_formula)!=NULL && (yysemantic_stack_[(3) - (3)]._modal_formula)!=NULL)
    (yyval._modal_formula) = new modal_formula(1, (yysemantic_stack_[(3) - (1)]._modal_formula), (yysemantic_stack_[(3) - (3)]._modal_formula));
  else
    (yyval._modal_formula) = NULL;
 }
    break;

  case 631:

/* Line 690 of lalr1.cc  */
#line 4086 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._modal_formula)!=NULL && (yysemantic_stack_[(3) - (3)]._modal_formula)!=NULL)
    (yyval._modal_formula) = new modal_formula(2, (yysemantic_stack_[(3) - (1)]._modal_formula), (yysemantic_stack_[(3) - (3)]._modal_formula));
  else
    (yyval._modal_formula) = NULL;
 }
    break;

  case 632:

/* Line 690 of lalr1.cc  */
#line 4092 "parser/nssis_new.yy"
    {
  (yyval._modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)]._modal_formula));USE((yysemantic_stack_[(3) - (3)]._modal_formula));
 }
    break;

  case 633:

/* Line 690 of lalr1.cc  */
#line 4097 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)]._modal_formula)!=NULL)
    (yyval._modal_formula) = new modal_formula(3, (yysemantic_stack_[(2) - (2)]._modal_formula));
  else
    (yyval._modal_formula) = NULL;
 }
    break;

  case 634:

/* Line 690 of lalr1.cc  */
#line 4103 "parser/nssis_new.yy"
    {
  (yyval._modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(2) - (2)]._modal_formula));
 }
    break;

  case 635:

/* Line 690 of lalr1.cc  */
#line 4108 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)]._modal_formula)!=NULL && (yysemantic_stack_[(3) - (3)]._modal_formula)!=NULL)
    (yyval._modal_formula) = new modal_formula(4, (yysemantic_stack_[(3) - (1)]._modal_formula), (yysemantic_stack_[(3) - (3)]._modal_formula));
  else
    (yyval._modal_formula) = NULL;
 }
    break;

  case 636:

/* Line 690 of lalr1.cc  */
#line 4114 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)]._modal_formula)!=NULL)
    (yyval._modal_formula) = new modal_formula(10, (yysemantic_stack_[(2) - (2)]._modal_formula));
  else
    (yyval._modal_formula) = NULL;
 }
    break;

  case 637:

/* Line 690 of lalr1.cc  */
#line 4120 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)]._modal_formula)!=NULL)
    (yyval._modal_formula) = new modal_formula(11, (yysemantic_stack_[(2) - (2)]._modal_formula));
  else
    (yyval._modal_formula) = NULL;
  }
    break;

  case 638:

/* Line 690 of lalr1.cc  */
#line 4126 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)]._modal_formula)!=NULL)
    (yyval._modal_formula) = new modal_formula(12, (yysemantic_stack_[(2) - (2)]._modal_formula));
  else
    (yyval._modal_formula) = NULL;
 }
    break;

  case 639:

/* Line 690 of lalr1.cc  */
#line 4132 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)]._modal_formula)!=NULL)
    (yyval._modal_formula) = new modal_formula(13, (yysemantic_stack_[(2) - (2)]._modal_formula));
  else
    (yyval._modal_formula) = NULL;
 }
    break;

  case 640:

/* Line 690 of lalr1.cc  */
#line 4138 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)]._modal_formula)!=NULL)
    (yyval._modal_formula) = new modal_formula(14, (yysemantic_stack_[(2) - (2)]._modal_formula));
  else
    (yyval._modal_formula) = NULL;
 }
    break;

  case 641:

/* Line 690 of lalr1.cc  */
#line 4144 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)]._modal_formula)!=NULL)
    (yyval._modal_formula) = new modal_formula(15, (yysemantic_stack_[(2) - (2)]._modal_formula));
  else
    (yyval._modal_formula) = NULL;
 }
    break;

  case 642:

/* Line 690 of lalr1.cc  */
#line 4150 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)].dual_modal_formula)!=NULL) {
    (yyval._modal_formula) = new modal_formula(16, (yysemantic_stack_[(2) - (2)].dual_modal_formula)->first, (yysemantic_stack_[(2) - (2)].dual_modal_formula)->second);
    free((yysemantic_stack_[(2) - (2)].dual_modal_formula));
  }
  else
    (yyval._modal_formula) = NULL;
 }
    break;

  case 643:

/* Line 690 of lalr1.cc  */
#line 4158 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)].dual_modal_formula)!=NULL) {
    (yyval._modal_formula) = new modal_formula(17, (yysemantic_stack_[(2) - (2)].dual_modal_formula)->first, (yysemantic_stack_[(2) - (2)].dual_modal_formula)->second);
    free((yysemantic_stack_[(2) - (2)].dual_modal_formula));
  }
  else
    (yyval._modal_formula) = NULL;
 }
    break;

  case 644:

/* Line 690 of lalr1.cc  */
#line 4166 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(2) - (2)].ID_modal_formula)!=NULL) {
    atomic_proposition *ap = new atomic_proposition((yysemantic_stack_[(2) - (2)].ID_modal_formula)->first);
    modal_formula *a = new modal_formula(ap);
    (yyval._modal_formula) = new modal_formula(30, a, (yysemantic_stack_[(2) - (2)].ID_modal_formula)->second);
    free((yysemantic_stack_[(2) - (2)].ID_modal_formula));
  } else
    (yyval._modal_formula) = NULL;
 }
    break;

  case 645:

/* Line 690 of lalr1.cc  */
#line 4175 "parser/nssis_new.yy"
    {
  // Knowledge in a group (everybody knows)
  if((yysemantic_stack_[(2) - (2)].ID_modal_formula)!=NULL) {
    atomic_proposition *ap = new atomic_proposition((yysemantic_stack_[(2) - (2)].ID_modal_formula)->first);
    modal_formula *a = new modal_formula(ap);
    (yyval._modal_formula) = new modal_formula(31, a, (yysemantic_stack_[(2) - (2)].ID_modal_formula)->second);
    free((yysemantic_stack_[(2) - (2)].ID_modal_formula));
  } else
    (yyval._modal_formula) = NULL;
 }
    break;

  case 646:

/* Line 690 of lalr1.cc  */
#line 4185 "parser/nssis_new.yy"
    {
  // Common knowledge in a group
  if((yysemantic_stack_[(2) - (2)].ID_modal_formula)!=NULL) {
    atomic_proposition *ap = new atomic_proposition((yysemantic_stack_[(2) - (2)].ID_modal_formula)->first);
    modal_formula *a = new modal_formula(ap);
    (yyval._modal_formula) = new modal_formula(32, a, (yysemantic_stack_[(2) - (2)].ID_modal_formula)->second);
    free((yysemantic_stack_[(2) - (2)].ID_modal_formula));
  } else
    (yyval._modal_formula) = NULL;
 }
    break;

  case 647:

/* Line 690 of lalr1.cc  */
#line 4195 "parser/nssis_new.yy"
    {
  // deontic operator
  if((yysemantic_stack_[(2) - (2)].ID_modal_formula)!=NULL) {
    atomic_proposition *ap = new atomic_proposition((yysemantic_stack_[(2) - (2)].ID_modal_formula)->first);
    modal_formula *a = new modal_formula(ap);
    (yyval._modal_formula) = new modal_formula(40, a, (yysemantic_stack_[(2) - (2)].ID_modal_formula)->second);
    free((yysemantic_stack_[(2) - (2)].ID_modal_formula));
  } else
    (yyval._modal_formula) = NULL;
 }
    break;

  case 648:

/* Line 690 of lalr1.cc  */
#line 4205 "parser/nssis_new.yy"
    {
  // Distributed knowledge in a group
  if((yysemantic_stack_[(2) - (2)].ID_modal_formula)!=NULL) {
    atomic_proposition *ap = new atomic_proposition((yysemantic_stack_[(2) - (2)].ID_modal_formula)->first);
    modal_formula *a = new modal_formula(ap);
    (yyval._modal_formula) = new modal_formula(42, a, (yysemantic_stack_[(2) - (2)].ID_modal_formula)->second);
    free((yysemantic_stack_[(2) - (2)].ID_modal_formula));
  } else
    (yyval._modal_formula) = NULL;
 }
    break;

  case 649:

/* Line 690 of lalr1.cc  */
#line 4215 "parser/nssis_new.yy"
    { 
  (yyval._modal_formula) = NULL;
  driver.syntax_error = true;
 }
    break;

  case 650:

/* Line 690 of lalr1.cc  */
#line 4219 "parser/nssis_new.yy"
    { 
  (yyval._modal_formula) = NULL;
  driver.syntax_error = true;
 }
    break;

  case 651:

/* Line 690 of lalr1.cc  */
#line 4223 "parser/nssis_new.yy"
    {
  // ATL X operator
  if((yysemantic_stack_[(3) - (1)].sval)!=NULL && (yysemantic_stack_[(3) - (3)]._modal_formula)!=NULL) {
    atomic_proposition *ap = new atomic_proposition((yysemantic_stack_[(3) - (1)].sval));
    modal_formula *a = new modal_formula(ap);
    (yyval._modal_formula) = new modal_formula(45, a, (yysemantic_stack_[(3) - (3)]._modal_formula));
  } else
    (yyval._modal_formula) = NULL;
 }
    break;

  case 652:

/* Line 690 of lalr1.cc  */
#line 4232 "parser/nssis_new.yy"
    {
  // ATL F operator
  if((yysemantic_stack_[(3) - (1)].sval)!=NULL && (yysemantic_stack_[(3) - (3)]._modal_formula)!=NULL) {
    atomic_proposition *ap = new atomic_proposition((yysemantic_stack_[(3) - (1)].sval));
    modal_formula *a = new modal_formula(ap);
    (yyval._modal_formula) = new modal_formula(46, a, (yysemantic_stack_[(3) - (3)]._modal_formula));
  } else
    (yyval._modal_formula) = NULL;
 }
    break;

  case 653:

/* Line 690 of lalr1.cc  */
#line 4241 "parser/nssis_new.yy"
    {
  // ATL G operator
  if((yysemantic_stack_[(3) - (1)].sval)!=NULL && (yysemantic_stack_[(3) - (3)]._modal_formula)!=NULL) {
    atomic_proposition *ap = new atomic_proposition((yysemantic_stack_[(3) - (1)].sval));
    modal_formula *a = new modal_formula(ap);
    (yyval._modal_formula) = new modal_formula(47, a, (yysemantic_stack_[(3) - (3)]._modal_formula));
  } else
    (yyval._modal_formula) = NULL;
 }
    break;

  case 654:

/* Line 690 of lalr1.cc  */
#line 4250 "parser/nssis_new.yy"
    {
  (yyval._modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (3)]._modal_formula));
 }
    break;

  case 655:

/* Line 690 of lalr1.cc  */
#line 4255 "parser/nssis_new.yy"
    {
  // ATL U operator
  if((yysemantic_stack_[(2) - (1)].sval)!=NULL && (yysemantic_stack_[(2) - (2)].dual_modal_formula)!=NULL) {
    atomic_proposition *ap = new atomic_proposition((yysemantic_stack_[(2) - (1)].sval));
    modal_formula *a = new modal_formula(ap);
    (yyval._modal_formula) = new modal_formula(48, a, (yysemantic_stack_[(2) - (2)].dual_modal_formula)->first, (yysemantic_stack_[(2) - (2)].dual_modal_formula)->second);
    free((yysemantic_stack_[(2) - (2)].dual_modal_formula));
  } else {
    if((yysemantic_stack_[(2) - (2)].dual_modal_formula) != NULL)
       free((yysemantic_stack_[(2) - (2)].dual_modal_formula));
    if((yysemantic_stack_[(2) - (1)].sval) != NULL)
      free((yysemantic_stack_[(2) - (1)].sval));
    (yyval._modal_formula) = NULL;
  }
 }
    break;

  case 656:

/* Line 690 of lalr1.cc  */
#line 4270 "parser/nssis_new.yy"
    {	
  if((yysemantic_stack_[(1) - (1)].sval)!=NULL) {
    atomic_proposition *ap;
    int i = search_string_table((yysemantic_stack_[(1) - (1)].sval));
    if(i>=0) {
      ap = new atomic_proposition((*string_table)[i]);
      free((yysemantic_stack_[(1) - (1)].sval));
    } else {
      ap = new atomic_proposition((yysemantic_stack_[(1) - (1)].sval));
      string_table->push_back((yysemantic_stack_[(1) - (1)].sval));
    }
    (yyval._modal_formula) = new modal_formula(ap);
  } else
    (yyval._modal_formula) = NULL;
  }
    break;

  case 657:

/* Line 690 of lalr1.cc  */
#line 4285 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].sval)!=NULL) {
    string *newname = new string(*(yysemantic_stack_[(3) - (1)].sval) + ".GreenStates");
    atomic_proposition *ap;
    int i = search_string_table(newname);
    if(i>=0) {
      ap = new atomic_proposition((*string_table)[i]);
      free(newname);
    } else {
      ap = new atomic_proposition(newname);
      string_table->push_back(newname);
    }
    free((yysemantic_stack_[(3) - (1)].sval));
    (yyval._modal_formula) = new modal_formula(ap);
  } else
    (yyval._modal_formula) = NULL;
 }
    break;

  case 658:

/* Line 690 of lalr1.cc  */
#line 4302 "parser/nssis_new.yy"
    {
  if((yysemantic_stack_[(3) - (1)].sval)!=NULL) {
    string *newname = new string(*(yysemantic_stack_[(3) - (1)].sval) + ".RedStates");
    atomic_proposition *ap;
    int i = search_string_table(newname);
    if(i>=0) {
      ap = new atomic_proposition((*string_table)[i]);
      free(newname);
    } else {
      ap = new atomic_proposition(newname);
      string_table->push_back(newname);
    }
    free((yysemantic_stack_[(3) - (1)].sval));
    (yyval._modal_formula) = new modal_formula(ap);
  } else
    (yyval._modal_formula) = NULL;
 }
    break;

  case 659:

/* Line 690 of lalr1.cc  */
#line 4319 "parser/nssis_new.yy"
    {
    string *newname = new string("Environment.GreenStates");
    atomic_proposition *ap;
    int i = search_string_table(newname);
    if(i>=0) {
      ap = new atomic_proposition((*string_table)[i]);
      free(newname);
    } else {
      ap = new atomic_proposition(newname);
      string_table->push_back(newname);
    }
    (yyval._modal_formula) = new modal_formula(ap);
 }
    break;

  case 660:

/* Line 690 of lalr1.cc  */
#line 4332 "parser/nssis_new.yy"
    {
  string *newname = new string("Environment.RedStates");
  atomic_proposition *ap;
  int i = search_string_table(newname);
  if(i>=0) {
    ap = new atomic_proposition((*string_table)[i]);
    free(newname);
  } else {
    ap = new atomic_proposition(newname);
    string_table->push_back(newname);
  }
  (yyval._modal_formula) = new modal_formula(ap);
 }
    break;

  case 661:

/* Line 690 of lalr1.cc  */
#line 4345 "parser/nssis_new.yy"
    {
  (yyval._modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)].sval));
 }
    break;

  case 662:

/* Line 690 of lalr1.cc  */
#line 4350 "parser/nssis_new.yy"
    {
  (yyval._modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)].sval));
 }
    break;

  case 663:

/* Line 690 of lalr1.cc  */
#line 4355 "parser/nssis_new.yy"
    {
  (yyval._modal_formula) = NULL;
  driver.syntax_error = true;
  USE((yysemantic_stack_[(3) - (1)].sval));
 }
    break;

  case 664:

/* Line 690 of lalr1.cc  */
#line 4360 "parser/nssis_new.yy"
    {
  (yyval._modal_formula) = NULL;
  driver.syntax_error = true;
  }
    break;



/* Line 690 of lalr1.cc  */
#line 8725 "parser/nssis.cc"
	default:
          break;
      }
    /* User semantic actions sometimes alter yychar, and that requires
       that yytoken be updated with the new translation.  We take the
       approach of translating immediately before every use of yytoken.
       One alternative is translating here after every semantic action,
       but that translation would be missed if the semantic action
       invokes YYABORT, YYACCEPT, or YYERROR immediately after altering
       yychar.  In the case of YYABORT or YYACCEPT, an incorrect
       destructor might then be invoked immediately.  In the case of
       YYERROR, subsequent parser actions might lead to an incorrect
       destructor call or verbose syntax error message before the
       lookahead is translated.  */
    YY_SYMBOL_PRINT ("-> $$ =", yyr1_[yyn], &yyval, &yyloc);

    yypop_ (yylen);
    yylen = 0;
    YY_STACK_PRINT ();

    yysemantic_stack_.push (yyval);
    yylocation_stack_.push (yyloc);

    /* Shift the result of the reduction.  */
    yyn = yyr1_[yyn];
    yystate = yypgoto_[yyn - yyntokens_] + yystate_stack_[0];
    if (0 <= yystate && yystate <= yylast_
	&& yycheck_[yystate] == yystate_stack_[0])
      yystate = yytable_[yystate];
    else
      yystate = yydefgoto_[yyn - yyntokens_];
    goto yynewstate;

  /*------------------------------------.
  | yyerrlab -- here on detecting error |
  `------------------------------------*/
  yyerrlab:
    /* Make sure we have latest lookahead translation.  See comments at
       user semantic actions for why this is necessary.  */
    yytoken = yytranslate_ (yychar);

    /* If not already recovering from an error, report this error.  */
    if (!yyerrstatus_)
      {
	++yynerrs_;
	if (yychar == yyempty_)
	  yytoken = yyempty_;
	error (yylloc, yysyntax_error_ (yystate, yytoken));
      }

    yyerror_range[1] = yylloc;
    if (yyerrstatus_ == 3)
      {
	/* If just tried and failed to reuse lookahead token after an
	 error, discard it.  */

	if (yychar <= yyeof_)
	  {
	  /* Return failure if at end of input.  */
	  if (yychar == yyeof_)
	    YYABORT;
	  }
	else
	  {
	    yydestruct_ ("Error: discarding", yytoken, &yylval, &yylloc);
	    yychar = yyempty_;
	  }
      }

    /* Else will try to reuse lookahead token after shifting the error
       token.  */
    goto yyerrlab1;


  /*---------------------------------------------------.
  | yyerrorlab -- error raised explicitly by YYERROR.  |
  `---------------------------------------------------*/
  yyerrorlab:

    /* Pacify compilers like GCC when the user code never invokes
       YYERROR and the label yyerrorlab therefore never appears in user
       code.  */
    if (false)
      goto yyerrorlab;

    yyerror_range[1] = yylocation_stack_[yylen - 1];
    /* Do not reclaim the symbols of the rule which action triggered
       this YYERROR.  */
    yypop_ (yylen);
    yylen = 0;
    yystate = yystate_stack_[0];
    goto yyerrlab1;

  /*-------------------------------------------------------------.
  | yyerrlab1 -- common code for both syntax error and YYERROR.  |
  `-------------------------------------------------------------*/
  yyerrlab1:
    yyerrstatus_ = 3;	/* Each real token shifted decrements this.  */

    for (;;)
      {
	yyn = yypact_[yystate];
	if (!yy_pact_value_is_default_ (yyn))
	{
	  yyn += yyterror_;
	  if (0 <= yyn && yyn <= yylast_ && yycheck_[yyn] == yyterror_)
	    {
	      yyn = yytable_[yyn];
	      if (0 < yyn)
		break;
	    }
	}

	/* Pop the current state because it cannot handle the error token.  */
	if (yystate_stack_.height () == 1)
	YYABORT;

	yyerror_range[1] = yylocation_stack_[0];
	yydestruct_ ("Error: popping",
		     yystos_[yystate],
		     &yysemantic_stack_[0], &yylocation_stack_[0]);
	yypop_ ();
	yystate = yystate_stack_[0];
	YY_STACK_PRINT ();
      }

    yyerror_range[2] = yylloc;
    // Using YYLLOC is tempting, but would change the location of
    // the lookahead.  YYLOC is available though.
    YYLLOC_DEFAULT (yyloc, yyerror_range, 2);
    yysemantic_stack_.push (yylval);
    yylocation_stack_.push (yyloc);

    /* Shift the error token.  */
    YY_SYMBOL_PRINT ("Shifting", yystos_[yyn],
		     &yysemantic_stack_[0], &yylocation_stack_[0]);

    yystate = yyn;
    goto yynewstate;

    /* Accept.  */
  yyacceptlab:
    yyresult = 0;
    goto yyreturn;

    /* Abort.  */
  yyabortlab:
    yyresult = 1;
    goto yyreturn;

  yyreturn:
    if (yychar != yyempty_)
      {
        /* Make sure we have latest lookahead translation.  See comments
           at user semantic actions for why this is necessary.  */
        yytoken = yytranslate_ (yychar);
        yydestruct_ ("Cleanup: discarding lookahead", yytoken, &yylval,
                     &yylloc);
      }

    /* Do not reclaim the symbols of the rule which action triggered
       this YYABORT or YYACCEPT.  */
    yypop_ (yylen);
    while (yystate_stack_.height () != 1)
      {
	yydestruct_ ("Cleanup: popping",
		   yystos_[yystate_stack_[0]],
		   &yysemantic_stack_[0],
		   &yylocation_stack_[0]);
	yypop_ ();
      }

    return yyresult;
  }

  // Generate an error message.
  std::string
  mcmas_parser::yysyntax_error_ (int yystate, int yytoken)
  {
    std::string yyres;
    // Number of reported tokens (one for the "unexpected", one per
    // "expected").
    size_t yycount = 0;
    // Its maximum.
    enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
    // Arguments of yyformat.
    char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];

    /* There are many possibilities here to consider:
       - If this state is a consistent state with a default action, then
         the only way this function was invoked is if the default action
         is an error action.  In that case, don't check for expected
         tokens because there are none.
       - The only way there can be no lookahead present (in yytoken) is
         if this state is a consistent state with a default action.
         Thus, detecting the absence of a lookahead is sufficient to
         determine that there is no unexpected or expected token to
         report.  In that case, just report a simple "syntax error".
       - Don't assume there isn't a lookahead just because this state is
         a consistent state with a default action.  There might have
         been a previous inconsistent state, consistent state with a
         non-default action, or user semantic action that manipulated
         yychar.
       - Of course, the expected token list depends on states to have
         correct lookahead information, and it depends on the parser not
         to perform extra reductions after fetching a lookahead from the
         scanner and before detecting a syntax error.  Thus, state
         merging (from LALR or IELR) and default reductions corrupt the
         expected token list.  However, the list is correct for
         canonical LR with one exception: it will still contain any
         token that will not be accepted due to an error action in a
         later state.
    */
    if (yytoken != yyempty_)
      {
        yyarg[yycount++] = yytname_[yytoken];
        int yyn = yypact_[yystate];
        if (!yy_pact_value_is_default_ (yyn))
          {
            /* Start YYX at -YYN if negative to avoid negative indexes in
               YYCHECK.  In other words, skip the first -YYN actions for
               this state because they are default actions.  */
            int yyxbegin = yyn < 0 ? -yyn : 0;
            /* Stay within bounds of both yycheck and yytname.  */
            int yychecklim = yylast_ - yyn + 1;
            int yyxend = yychecklim < yyntokens_ ? yychecklim : yyntokens_;
            for (int yyx = yyxbegin; yyx < yyxend; ++yyx)
              if (yycheck_[yyx + yyn] == yyx && yyx != yyterror_
                  && !yy_table_value_is_error_ (yytable_[yyx + yyn]))
                {
                  if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
                    {
                      yycount = 1;
                      break;
                    }
                  else
                    yyarg[yycount++] = yytname_[yyx];
                }
          }
      }

    char const* yyformat = 0;
    switch (yycount)
      {
#define YYCASE_(N, S)                         \
        case N:                               \
          yyformat = S;                       \
        break
        YYCASE_(0, YY_("syntax error"));
        YYCASE_(1, YY_("syntax error, unexpected %s"));
        YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
        YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
        YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
        YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
#undef YYCASE_
      }

    // Argument number.
    size_t yyi = 0;
    for (char const* yyp = yyformat; *yyp; ++yyp)
      if (yyp[0] == '%' && yyp[1] == 's' && yyi < yycount)
        {
          yyres += yytnamerr_ (yyarg[yyi++]);
          ++yyp;
        }
      else
        yyres += *yyp;
    return yyres;
  }


  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
  const short int mcmas_parser::yypact_ninf_ = -910;
  const short int
  mcmas_parser::yypact_[] =
  {
       239,   620,    55,    74,   193,  1369,  -910,  2630,  1798,   728,
     313,  -910,  -910,  -910,  -910,    43,  -910,   212,  -910,  1301,
    1125,   702,  1022,  1048,   136,  1564,   176,   604,   910,  1273,
     102,   355,   363,  -910,   728,   186,  -910,  -910,   133,   167,
    1003,   565,   680,  -910,   431,   305,   704,  1398,  -910,  -910,
    -910,  -910,  -910,  -910,   671,    51,  1089,  -910,   320,   324,
    1552,   604,  1273,   355,  1085,   883,   403,  -910,  2092,  1273,
     355,  1149,   348,  2895,  -910,  -910,   697,  2895,  1674,  -910,
    -910,  -910,  -910,  1099,   693,  5874,  5508,  -910,  2282,  6138,
    -910,  -910,  -910,  -910,  1815,   355,  1169,   347,  -910,  -910,
     896,   673,  1168,   653,  1011,   167,  -910,  1134,   494,  1644,
    -910,  1193,   710,  5228,  1270,   178,  1548,   540,  1092,  -910,
    -910,  -910,  -910,  -910,  -910,  -910,  -910,  -910,  -910,   465,
     545,  1016,  -910,   561,  -910,  -910,   528,  1273,   355,   355,
    1011,  -910,  -910,  -910,  1268,  -910,  -910,   355,  1011,  1825,
    -910,  -910,  1806,  5906,   797,  -910,  -910,  -910,  1355,  6605,
    2746,  -910,  3998,  1857,  1420,  -910,   866,  -910,  1029,  2895,
    2895,  -910,  1736,  1736,  1736,  1736,  1736,  1736,  1420,  -910,
    -910,  -910,  -910,  -910,  -910,  1420,  1420,  1420,  1420,  1420,
    1011,  -910,  -910,  -910,   180,   754,  -910,  -910,  -910,  -910,
    1254,   495,  1218,  -910,  2693,  -910,  1336,  1490,   791,  1229,
     125,  1619,   710,  2857,  2857,   890,    87,  1432,  -910,   850,
    1193,   447,  1193,   518,  1341,   670,  -910,  -910,  -910,   581,
     656,  5076,   216,  5137,  -910,  -910,  1497,  -910,   982,  1559,
    1028,   403,  1693,  1296,  1294,   236,   800,  1214,   682,  -910,
    -910,   941,  1400,  1548,   267,  -910,  -910,   992,   898,   267,
     346,  -910,   912,  -910,  -910,   355,  1011,  1011,  1619,  1011,
    1619,   907,  -910,  -910,  -910,  2529,  -910,  2114,  -910,  2381,
    -910,  2895,  1857,   197,   629,  5052,  5164,  5250,  2146,  1736,
    5542,  5574,  5608,  -910,  -910,  -910,  6170,  6204,  6236,  1620,
    -910,  -910,  1619,  -910,  -910,  1925,  -910,  1560,   361,  -910,
    -910,  1025,   361,  1323,  -910,  -910,  1336,  1111,  -910,  2880,
     361,  -910,  -910,  -910,  1091,  1194,   400,  1136,  -910,   266,
    -910,  1796,  1291,  1901,  -910,   656,   216,  -910,  1701,  2857,
     737,  2857,   472,  5772,  -910,  2962,  6489,  -910,  -910,  5398,
    5940,  -910,  -910,  -910,  1782,  2165,  -910,  -910,  -910,  2857,
    2857,  1181,   798,   877,  1621,  1201,  1242,  1151,  1282,  1346,
    5481,  1193,  1193,  1747,  -910,   337,   357,  1331,  -910,   584,
    1160,   216,  -910,  2965,   745,  5395,  1156,  5395,  5395,  5395,
    5395,  5395,  5395,  5395,  1477,  1477,  1494,  1500,  1500,  1494,
    1500,  6723,  -910,  5162,   639,  -910,  -910,  3906,  5223,  1371,
    1397,  5223,  5223,  5223,  5223,  5223,  5223,  5223,  1633,  1633,
    1638,  1691,  1691,  1638,  1691,  6734,  4902,   598,  1481,  -910,
    -910,  -910,  -910,  -910,  -910,  1117,  2918,   803,  2918,   993,
    -910,  -910,  -910,  1099,  2192,  4966,  6270,  -910,  -910,  5972,
    5640,  -910,  -910,  -910,  1998,   800,  -910,   896,   794,  2695,
    1309,  -910,  -910,  -910,   489,  1382,  -910,  1294,   800,  -910,
    1407,  -910,  1433,    31,    31,  -910,  1097,    31,    31,  1011,
    1619,  1619,  -910,  1619,  -910,  1879,  2105,  -910,  -910,  -910,
    -910,  -910,  -910,  1285,  1285,  -910,  1285,  -910,  -910,  -910,
    -910,  1724,  1420,  1293,  -910,  -910,  2933,   400,  -910,  -910,
    -910,   216,  -910,  -910,  1473,  4876,  -910,  6302,  1678,  5050,
    6633,  1684,  1516,  1581,  1802,  1958,   810,  -910,  1601,  1647,
     810,   810,   810,   810,   810,   810,  1482,  1482,  1482,  1482,
    1482,  1482,  2718,  2857,  2857,  -910,  2756,  -910,  2272,  2547,
    1630,   315,   390,  1428,  -910,  1744,  -910,  1340,  1366,  1193,
    1402,  1404,   227,  -910,  1902,  2289,  2681,  1591,   342,  -910,
    -910,  -910,  1681,  1607,   380,  1679,  1331,  -910,  -910,  3933,
    5420,  -910,  -910,  -910,  2690,  -910,  -910,  3994,  1563,   601,
    5104,  6735,  6736,  6747,  6758,  6792,  6795,  5395,  5395,  -910,
    -910,   108,   135,  -910,  1698,  1722,  -910,  -910,  -910,  -910,
    1703,  1090,  4022,  -910,  1980,  5248,  5395,  5395,  -910,  5395,
    3026,  5309,  6675,  -910,  -910,  6808,  3053,  1911,  1219,  1718,
    6812,  6824,  6837,  6861,  6872,  6874,  6885,  5223,  5223,  -910,
    -910,   185,   263,  -910,  1741,  1745,  -910,  -910,  -910,  -910,
    1824,  1195,  2189,   338,  -910,  2074,  5223,  5223,  5223,  5223,
    -910,  4963,  5223,  5223,  -910,  5223,  1385,  1751,  5336,  6307,
    -910,  6006,  1805,  6371,  6653,  1755,  1760,  5337,  1447,  1358,
    -910,  -910,  2779,  2918,  2918,  -910,  1358,  1358,  1358,  1358,
    1358,  1358,  1611,  1611,  1611,  1611,  1611,  1611,  1309,  -910,
    1509,  1191,  -910,  1336,  2000,   969,   627,  1748,  -910,  -910,
     800,  1309,  -910,  -910,  1795,  -910,  -910,  1407,  -910,  -910,
    -910,  1619,  -910,  -910,  -910,   512,   709,  1817,  -910,  -910,
    -910,  -910,  1012,  2020,  2933,  1419,  2933,  6333,  2282,  2582,
    -910,  -910,  -910,  -910,  -910,  2553,  -910,  2413,  -910,  2312,
    -910,  2591,  -910,  -910,  -910,  2857,  1958,   692,   706,  -910,
    -910,  6527,  6547,  6585,  2244,  -910,  -910,  2250,  1482,  6038,
    6072,  6104,  -910,  -910,  -910,  3139,  3206,  3294,  2781,  -910,
    2803,  -910,   390,  1094,  -910,  -910,  -910,  -910,  -910,   390,
     390,   390,   552,   390,   390,   390,   868,  -910,  -910,  -910,
    -910,  -910,  -910,  -910,  -910,  -910,  -910,  -910,  1376,  -910,
     380,   779,  6686,   815,  4957,  4083,  -910,  4110,  -910,  -910,
    -910,  5395,  1495,  1858,    77,   404,   429,   733,   806,   824,
    -910,  -910,  -910,  -910,  -910,  5334,  -910,  6896,  6909,  6933,
    6939,   860,  6673,   869,  5303,  -910,  3114,  -910,  3141,  -910,
    -910,  -910,  -910,  -910,  5223,  2147,  2176,   880,   911,   938,
     949,   985,   998,  -910,  -910,  -910,  -910,  -910,  -910,  -910,
    -910,  4988,  -910,  6957,  6963,  6981,  6987,  7005,  7011,  7029,
    7035,  -910,   559,  -910,  -910,  -910,  2435,  -910,  2344,  -910,
    2052,  -910,  -910,  -910,  2918,  1447,   929,  1015,  5399,  5543,
    5875,  6340,  6401,  6420,  2572,  -910,  -910,  1763,  1611,  5674,
    5706,  5740,  -910,  -910,  -910,  1748,  1577,  1047,  -910,  -910,
    1336,  -910,  2839,   361,   103,   665,  1886,  1078,   344,  -910,
    1910,  1916,  -910,  1309,  1748,  -910,  -910,  -910,  -910,  -910,
    -910,  1844,  5806,   797,  3382,  2746,  1899,  1849,  1856,  3470,
     375,   974,  1420,  2933,  2933,  2933,  -910,  2346,  2432,  -910,
    -910,  -910,  -910,  1890,  1891,  -910,  -910,  -910,  -910,  1915,
    1919,  -910,    67,   717,   570,  -910,  1376,  5395,  5395,  5049,
    5395,  5395,  5395,  5049,  5395,  5395,  5395,  5395,  5395,  5395,
    5395,  5395,  5395,  5395,  5395,  5395,  5395,  5223,  5223,  4875,
    5223,  5223,  5223,  4875,  5223,  5223,  5223,  5223,  5223,  5223,
    5223,  5223,  5223,  5223,  5223,  5223,  5223,  2492,  2578,  -910,
    -910,  1285,  -910,  1725,  1358,  2842,  2842,   665,  1368,  -910,
    -910,  -910,  -910,  -910,  1748,  -910,  -910,  2614,  -910,  2638,
    -910,  -910,  -910,  1870,  1434,  -910,    56,  1466,  2942,  3558,
    3646,  3734,  1885,  1889,  1893,  1896,  -910,  -910,  -910,  -910,
    -910,  -910,  -910,  2481,  2494,  3915,  4077,  5492,  5494,  6440,
    6462,  2922,  6521,  5146,  7059,  7064,  7077,  7078,  7083,  7096,
    7101,  7107,  7112,  7118,  7130,  7131,  7136,  7155,  7160,  7171,
    7173,  7053,  7184,  5232,  7185,  7187,  7189,  7190,  7203,  7214,
    7232,  7237,  7238,  -910,  -910,  1557,  1639,  2842,   816,  1479,
    2842,  6467,  4966,  2820,  2871,  -910,  -910,  -910,  1897,  1900,
    1917,  -910,  1922,  1930,  -910,  -910,  -910,  -910,  4171,  -910,
    4198,  -910,  4259,  -910,  4286,  -910,  4347,  -910,  4374,  -910,
    4435,  -910,  4462,  -910,  4523,  -910,  4550,  -910,  4611,  -910,
    4638,  -910,  4259,  -910,  4286,  -910,  4435,  -910,  4462,  -910,
    4699,  -910,  4726,  -910,  4787,  -910,  4814,  -910,  3202,  -910,
    3229,  -910,  3290,  -910,  3317,  -910,  3378,  -910,  3405,  -910,
    3466,  -910,  3493,  -910,  3554,  -910,  3581,  -910,  3642,  -910,
    3669,  -910,  3290,  -910,  3317,  -910,  3466,  -910,  3493,  -910,
    3730,  -910,  3757,  -910,  3818,  -910,  3845,  -910,  1933,  5840,
    6307,  3822,  6371,  2003,   455,   412,  1934,  1935,  3931,   532,
    1026,  1358,   807,  2842,  2842,  -910,  2671,  -910,  -910,  -910,
    -910,  -910,  -910,  -910,  2467,  -910,  2505,  -910,  1937,  2009,
    4086,   101,  1594,  -910,  -910,  2842,  1939,  1596,  -910,   203,
    1612,  3051,  4174,  4175,  4262,  -910,  1942,  1943,  -910,  1946,
    1948,  -910,  1962,  1966,  1971,  -910,  1982,  1983,  -910,  -910,
    -910,  -910,  -910,  -910,  -910,  -910,  -910
  };

  /* YYDEFACT[S] -- default reduction number in state S.  Performed when
     YYTABLE doesn't specify something else to do.  Zero means the
     default is an error.  */
  const unsigned short int
  mcmas_parser::yydefact_[] =
  {
         0,    18,     0,     0,     0,     0,     2,     0,     0,     0,
       0,   123,    16,    17,    15,     0,     1,    18,     3,    83,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   125,   126,     0,   136,   409,   124,     0,     0,
       0,     0,     0,   160,     0,    82,   161,     0,    34,    32,
      69,    67,    81,    80,    39,     0,     0,    41,     0,     0,
      83,     0,     0,     0,    46,     0,     0,    76,    83,     0,
       0,     0,     0,     0,   390,   391,     0,     0,     0,   388,
      63,   389,    89,     0,     0,     0,     0,   257,     0,     0,
     268,   271,   261,   387,   163,     0,   167,     0,   173,   169,
       0,   180,     0,     0,     0,     0,   424,     0,     0,   437,
     436,     0,     0,    70,     0,     0,     0,     0,     0,     4,
       5,   162,   157,   158,   159,   156,    37,    38,    36,     0,
       0,    39,    40,     0,    43,    42,    82,     0,     0,     0,
       0,    72,    73,    71,    58,    75,    82,     0,     0,     0,
      85,    63,     0,     0,     0,   270,    86,    84,     0,     0,
       0,    64,     0,     0,     0,   269,    87,    88,     0,     0,
       0,    94,     0,     0,     0,     0,     0,     0,     0,   351,
     353,   355,   352,   354,   356,     0,     0,     0,     0,     0,
       0,   166,   165,   164,   167,     0,   168,   178,   179,   177,
       0,     0,     0,   188,     0,   194,     0,     0,   103,     0,
       0,     0,     0,     0,     0,   413,     0,     0,   414,     0,
       0,     0,     0,     0,     0,   501,   500,   473,   579,     0,
       0,     0,     0,     0,    14,   141,     0,    68,   142,     0,
      46,     0,    83,     0,     0,     0,     0,   148,     0,   152,
     150,     0,    70,     0,    62,    49,    59,     0,     0,    48,
       0,    47,     0,    45,    44,     0,     0,     0,     0,     0,
       0,     0,   229,   259,   273,     0,   228,     0,   258,     0,
     272,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   256,   254,   255,     0,     0,     0,     0,
     267,   266,     0,   175,   174,     0,   182,     0,     0,   183,
     181,   203,     0,     0,   185,   195,     0,   184,   187,     0,
       0,   101,   102,   100,   107,     0,     0,     0,   109,     0,
     110,     0,    22,     0,    30,     0,     0,    10,     0,     0,
       0,     0,     0,     0,   405,     0,     0,   296,   299,     0,
       0,   323,   398,   327,     0,     0,   411,   412,   410,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   446,   478,     0,     0,   480,     0,
     501,     0,    12,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   506,     0,     0,   580,    13,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   143,
     138,   139,   140,   137,    78,     0,     0,     0,     0,     0,
     393,   397,    92,     0,     0,     0,     0,   282,   285,     0,
       0,   311,   392,   315,   163,     0,   176,     0,   180,     0,
       0,   147,   146,   145,   148,     0,   149,     0,     0,    65,
      57,    55,     0,     0,     0,    62,     0,     0,     0,     0,
       0,     0,    28,     0,    26,     0,     0,    29,   201,   202,
     200,   217,   214,     0,     0,   186,     0,   105,   106,   104,
     118,     0,     0,   107,   108,   111,     0,     0,    20,    21,
      19,     0,     8,     9,     0,     0,   298,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   297,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   417,     0,   416,     0,     0,
       0,     0,     0,     0,   449,     0,   448,     0,     0,     0,
       0,     0,     0,   442,     0,     0,     0,   443,     0,   476,
     477,   475,   485,     0,     0,   478,     0,   479,    11,     0,
       0,   503,   568,   569,     0,   504,   502,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   561,
     562,     0,     0,   563,     0,     0,   564,   565,   566,   567,
       0,     0,     0,   507,     0,     0,     0,     0,   508,     0,
       0,     0,     0,   649,   650,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   642,
     643,     0,     0,   644,     0,     0,   645,   646,   647,   648,
       0,     0,     0,     0,   585,     0,     0,     0,     0,     0,
     655,     0,     0,     0,   586,     0,     0,     0,     0,     0,
     284,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     283,    91,     0,     0,     0,    97,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   171,
       0,     0,   197,     0,     0,   103,     0,     0,   154,   153,
       0,     0,    61,    60,    66,    53,    51,    56,    54,    52,
      50,     0,    24,    27,    25,   207,     0,     0,   213,   212,
     208,   115,     0,     0,     0,     0,     0,     0,     0,     0,
     116,     7,   403,   301,   325,     0,   426,     0,   300,     0,
     324,     0,   425,   404,   402,     0,     0,     0,     0,   401,
     400,     0,     0,     0,     0,   295,   294,     0,     0,     0,
       0,     0,   322,   320,   321,     0,     0,     0,     0,   421,
       0,   420,     0,     0,   408,   406,   471,   407,   469,     0,
       0,     0,     0,     0,     0,     0,     0,   444,   439,   440,
     441,   438,   483,   484,   482,   496,   497,   498,     0,   493,
       0,     0,     0,     0,     0,     0,   546,     0,   545,   574,
     573,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     577,   576,   575,   572,   571,     0,   510,     0,     0,     0,
       0,     0,     0,     0,     0,   593,     0,   627,     0,   626,
     592,   591,   660,   659,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   663,   662,   661,   658,   657,   582,   583,
     581,     0,   588,     0,     0,     0,     0,     0,     0,     0,
       0,   395,     0,   240,   287,   313,     0,   239,     0,   286,
       0,   312,   396,   394,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   281,   280,     0,     0,     0,
       0,     0,   310,   308,   309,     0,     0,     0,   190,   198,
       0,   192,     0,     0,   122,     0,     0,     0,     0,   220,
     131,     0,   133,     0,     0,    23,   205,   216,   206,   204,
     215,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   113,     0,     0,   470,
     468,   466,   467,     0,   407,   465,   463,   461,   462,     0,
     407,   460,     0,     0,     0,   490,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   132,
     191,     0,   122,     0,     0,     0,     0,     0,   107,   218,
     221,   129,   130,   128,     0,   135,   339,     0,   329,     0,
     328,   340,   338,     0,     0,   349,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   499,   487,   495,   488,
     486,   494,   491,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   210,   119,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   120,   134,   346,     0,     0,
       0,   347,     0,     0,   464,   459,   458,   457,     0,   533,
       0,   530,     0,   525,     0,   522,     0,   531,     0,   529,
       0,   523,     0,   521,     0,   517,     0,   514,     0,   515,
       0,   513,     0,   525,     0,   522,     0,   523,     0,   521,
       0,   541,     0,   538,     0,   539,     0,   537,     0,   614,
       0,   611,     0,   606,     0,   603,     0,   612,     0,   610,
       0,   604,     0,   602,     0,   598,     0,   595,     0,   596,
       0,   594,     0,   606,     0,   603,     0,   604,     0,   602,
       0,   622,     0,   619,     0,   620,     0,   618,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   224,     0,   223,   348,   343,
     344,   345,   342,   368,     0,   358,     0,   357,     0,     0,
     396,     0,     0,   369,   367,     0,     0,     0,   378,     0,
       0,     0,     0,     0,     0,   382,     0,     0,   383,     0,
       0,   375,     0,     0,     0,   376,     0,     0,   384,   380,
     381,   379,   377,   372,   373,   374,   371
  };

  /* YYPGOTO[NTERM-NUM].  */
  const short int
  mcmas_parser::yypgoto_[] =
  {
      -910,  -910,  -910,  2047,  -910,  -242,  -910,  -910,  2001,  -910,
      40,    41,  1803,   -28,   -10,   -45,  2031,  1952,   -89,   -65,
    1141,  1818,  -910,  -910,  -452,  -326,  -100,  -910,  1743,  -315,
    -909,  2075,  -910,  -880,   341,  -910,  1833,  -910,  -910,   -91,
     -90,   334,  -174,  1850,  -234,  -151,   260,  -424,  -910,  -910,
    -187,  -487,  1894,  1399,  -181,  -306,  -652,  -910,  1171,   672,
    -224,   -69,   -50,  1700,   -49,     9,  1035,   -37,  -374,  -605,
    1170,  -434,  -302,  -445,  1375,  -325,  -359,  -601,  1100,  -300,
    -440,  1437,  -464,  -316,  -906,  -910,   251,  -910,  -910,  -495,
    -910,  -910,  2067,  -910,  -150,  -910,  -910,  1999,   -38,  -910,
    1726,  1898,  1532,  1133,  -910,  1302,   971,  -910,  1710,  -179,
    -910,  1739,  1360,  1143,   256,  -910,  -910,  -165,  -910,  -910,
      15,  1342,  1250,   -43
  };

  /* YYDEFGOTO[NTERM-NUM].  */
  const short int
  mcmas_parser::yydefgoto_[] =
  {
        -1,     4,     5,     6,     7,   334,     8,    24,    57,    25,
      58,    59,   257,   441,    26,    67,    27,   116,    28,    82,
      29,   244,    83,   443,   210,   328,   211,   329,   330,   331,
     927,     9,    10,   932,    11,   117,   250,   118,   251,    30,
      99,    31,   246,   100,   103,   203,   104,   460,   204,   701,
     308,   728,   205,   702,   206,   493,   707,   928,   929,   152,
     668,    85,    86,    87,    88,    89,    90,    91,   445,   446,
     447,   448,   345,   346,   347,   348,   449,   450,   451,   349,
     350,   351,  1049,   187,  1252,    92,   452,   453,   353,   786,
      38,   218,    39,   108,   775,   111,   374,   112,   564,   229,
     378,   230,   574,   975,   379,   808,   809,   231,   402,   232,
     403,   599,   582,   583,   837,   233,   654,   234,   426,   427,
     639,   623,   624,   877
  };

  /* YYTABLE[YYPACT[STATE-NUM]].  What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule which
     number is the opposite.  If YYTABLE_NINF_, syntax error.  */
  const short int mcmas_parser::yytable_ninf_ = -665;
  const short int
  mcmas_parser::yytable_[] =
  {
        81,   670,   153,   504,   159,   680,   494,   729,   706,   730,
     196,   501,   459,   516,   496,   312,  1023,   527,   167,   444,
     320,   145,   154,   316,   160,   245,   482,   243,   484,   533,
     115,   698,   714,   336,   155,  1019,   515,   519,   517,   520,
     268,   165,   739,    81,   711,    81,   915,   337,   270,    81,
      81,   381,   127,   314,  1035,   318,    13,   788,    76,   934,
     487,   669,   673,   354,   355,   382,    66,   406,  1056,   128,
     455,  1120,    14,   224,  -489,    81,   671,   674,   977,   468,
     153,   901,   902,   903,   806,   761,   762,   763,   357,    15,
     302,   909,   910,   911,   153,   159,   769,   770,   771,   133,
     154,   258,   262,    96,    80,    41,    42,   133,   115,  1057,
    -222,  -222,   155,    97,   283,   284,  1257,   978,  1115,  1113,
    1114,    81,   290,   291,   292,   824,   324,  -126,  1121,   689,
     358,   153,   325,   326,   106,    81,    81,    54,   299,   807,
      81,    81,    81,    55,    81,    81,    81,    81,    81,    81,
      81,   154,   826,   245,  1116,   241,   511,    81,    81,    81,
      81,    81,   245,   155,   243,   495,   480,   481,   109,   483,
     512,   513,    81,  1258,    98,  -222,    81,    64,   442,   240,
     825,   363,   364,    65,   367,   344,   344,   296,   518,   521,
     428,   524,   740,    16,   297,   298,   434,   327,   178,   533,
    1211,  1213,   857,   533,  1218,   107,   274,   827,    56,   548,
     549,   110,   672,   153,   677,   -31,   578,   405,  1264,   485,
     486,   459,   191,   757,   758,   517,   520,   290,   797,    12,
    -415,   764,   670,   283,   459,   704,   153,   456,   722,   723,
       1,   724,     2,    81,   153,   155,   706,    81,    56,    81,
      56,    81,   303,    81,    81,  -125,   154,   858,  -127,   706,
      81,    81,   228,   185,   154,   186,   670,   503,   155,   944,
     946,   798,   949,   325,   326,  1265,   155,    81,   703,    93,
     859,  1034,   133,   901,  -127,    81,   933,   959,   296,   909,
     -66,    81,   669,   710,   960,   961,   962,   965,   966,   967,
     968,   971,   761,     3,   896,   897,   -33,   671,    98,   769,
     344,   344,   -33,   344,   344,   904,   714,  1253,  1254,   671,
     674,   131,    93,   140,    93,   134,   669,    55,    93,    93,
     148,   344,   344,   565,   566,   860,    74,    75,   327,   869,
     469,   671,    76,   800,  -492,  1028,   741,   475,   192,   156,
      37,   325,   925,   689,    93,   190,   101,   689,   570,    63,
     102,    70,   491,    95,   625,   627,   135,   699,   630,   631,
     632,   633,   634,   635,   636,    37,   245,   -33,   681,   721,
     157,   805,   569,   655,   870,    40,   801,   783,    80,   193,
    1043,   714,    56,   776,   777,   138,   139,   806,   266,   267,
      93,   500,   571,   147,   144,   989,  1044,   269,   326,  -492,
      65,    74,    75,  1241,    93,    93,   926,    76,   256,    93,
      93,    93,   952,    93,    93,    93,    93,    93,    93,    93,
     981,   516,   121,   492,   640,  -127,    93,    93,    93,    93,
      93,   122,   660,  1242,   990,   715,   716,  1045,   365,   719,
     720,    93,   807,   732,   757,    93,   517,   738,   898,   899,
     900,   670,   787,    80,   352,   352,   254,   957,   958,   982,
    1238,   265,   327,   525,    81,    56,   459,   704,    81,   935,
     526,   706,   670,   670,   893,   255,  1239,   404,   366,   340,
    1050,  1051,    76,    74,    75,   215,   309,   344,   344,    76,
     310,   216,   344,   344,   344,   344,   344,   344,   344,   344,
     344,   344,   344,   344,   344,   344,   344,   923,   344,   368,
     920,   896,    93,   784,   784,   479,    93,  1240,    93,   -68,
      93,   461,    93,    93,  1103,   -68,   671,   256,    80,    93,
      93,   247,   669,   669,   343,    80,   259,  1246,  1017,  1018,
     918,   248,   921,   714,   936,   260,    93,   671,   671,   369,
     666,   708,   263,  1247,    93,   261,   217,   436,  -242,   963,
      93,  1056,    76,    74,    75,  -242,   437,   625,   627,    76,
      74,    75,   375,   625,   937,   575,    76,   806,   376,   352,
     352,   376,   352,   352,   855,   856,  -242,   438,  -242,   656,
     -68,  -242,  1029,   264,  1248,    68,   638,   119,    20,   625,
     352,   352,   249,   873,   874,   875,   876,  1021,    80,   878,
     879,    -6,   880,    -6,   964,    80,   439,   952,   924,   952,
     279,   440,    80,   819,   820,   925,    23,    12,   280,   584,
     615,   588,   807,   590,   591,   592,   593,   594,   595,   596,
    1105,  1112,  1112,   377,   200,   616,   576,   380,   898,   614,
     201,    73,   898,  -125,   153,   159,  1022,   657,   658,   659,
     898,  -474,   670,   925,    74,    75,   617,  -474,   -46,  -189,
      76,   618,  -580,   462,   943,   945,   619,   738,   202,   126,
     226,    77,  -127,   530,   168,   185,   155,   186,   898,   926,
      84,   743,   228,    48,  -481,    81,    81,   747,    81,   169,
     938,   225,   197,   -58,   123,   748,  -481,   344,  1059,   344,
      78,   344,   120,   344,   463,    79,    80,   344,   344,    35,
     170,    33,  1210,  1212,   991,   171,  1112,   926,   522,   344,
     344,    49,  -474,   -46,   226,   158,   585,   671,   674,   162,
     344,   939,   344,    93,   784,   227,   228,    93,   531,  1060,
     532,   784,   784,   784,   784,   784,   784,   784,   784,  1020,
     161,    36,   531,   992,   532,   207,   352,   352,   523,   586,
     977,   352,   352,   352,   352,   352,   352,   352,   352,   352,
     352,   352,   352,   352,   352,   352,  1221,   352,   178,   551,
    -193,   458,   785,   785,   675,   102,   274,   993,  1106,   179,
     180,   756,   181,   552,  -226,  1107,   981,  1214,   526,   978,
     589,   182,   183,   184,  1108,   995,   304,   340,    74,    75,
     321,    74,    75,   197,    76,   584,   588,    76,  1109,   369,
     285,   286,   287,   584,   676,  1110,   994,  1251,  1112,  1112,
    1112,   219,  1112,   822,   823,   982,   589,  1215,   220,  -472,
    1112,   997,  1112,   185,   996,   186,  -472,   221,   584,   714,
    1001,  1112,   838,   839,   439,   840,   207,   342,   553,  1111,
      80,   997,   343,    80,   142,   969,   554,  -472,   222,    74,
      75,   361,  -472,   371,  1221,    76,  1221,   194,   150,   473,
     998,   629,   143,  1048,   738,   738,   738,    97,   149,  1002,
     629,    71,  1009,   477,   372,    73,  -231,    72,    73,  -456,
     998,   474,   362,  -231,    81,    81,    81,    81,    74,    75,
     686,    74,    75,   356,    76,   478,   195,    76,   884,  1001,
     970,    80,   464,   285,  -231,    77,  -231,   285,    77,  -231,
    1011,  1010,   248,   285,  1083,  1084,  1085,  1086,  1087,  1088,
    1089,  1090,  1091,  1092,  1093,  1094,  1095,  1096,  1097,  1098,
    1099,  1100,  1101,  1102,    78,  1046,  -219,    78,  1002,    79,
      80,   465,    79,    80,    93,    93,  1013,    93,   738,  1012,
     738,   285,   431,   470,   678,   687,   352,   688,   352,  1015,
     352,   679,   352,   471,   113,  1047,   352,   352,   321,    81,
     437,    81,   208,   178,    74,    75,   888,   209,   352,   352,
      76,  -117,    22,    50,   889,  1014,  -117,  1249,  -117,   352,
     149,   352,   472,   785,   126,   488,   -95,    73,  1016,   114,
     785,   785,   785,   785,   785,   785,   785,   785,   916,    52,
      74,    75,   306,  -184,  -211,   436,    76,  1250,   -58,   -66,
     -66,    51,   -66,  -249,   437,   440,    80,    77,    74,    75,
     -58,   -66,   -66,   -66,    76,   -66,   -66,   -66,   185,  1025,
     186,   687,  -211,   688,  -249,   438,   307,    53,   667,   -74,
     129,   832,  1026,   252,  1027,   793,    78,   497,   717,  -112,
     166,    79,    80,  -407,   141,  -118,    72,  -118,   718,   794,
    -407,    22,   -66,   -66,   439,   -66,   306,   -74,   666,   440,
     151,   -87,   833,   834,   -99,   436,    46,   -58,   130,   -66,
     -66,  -407,   -66,  -249,   437,   213,  -407,   472,    74,    75,
      47,   -66,   -66,   -66,    76,   -66,   -66,   -66,   214,   150,
     149,   502,   559,   -87,  -249,   438,   -96,    73,   667,  -249,
    -455,   -66,   -66,  -112,   -66,  -238,    62,  -455,    69,   198,
      74,    75,  -580,   -66,   -66,   -66,    76,   -66,   -66,   -66,
    -176,   150,   -66,   -66,   439,   -66,  -238,    77,  -455,   440,
     151,  -238,   917,  -455,   219,   498,   865,   589,   201,   436,
     499,   220,   137,    93,    93,    93,    93,   199,   437,  -176,
     221,   191,    74,    75,   -66,   -66,    78,   -66,    76,   311,
     850,    79,   151,   300,   301,  -155,   202,   866,   867,   438,
     322,   222,   851,  1063,  1064,  1065,  1066,  1067,  1068,  1069,
    1070,  1071,  1072,  1073,  1074,  1075,  1076,  1077,  1078,  1079,
    1080,  1081,  1082,   550,  -155,   305,   461,   307,   439,   306,
    -184,  -196,    73,   440,    80,   223,   -66,   -66,   323,   -66,
    -238,   238,   -74,   557,    94,    74,    75,    20,   -66,   -66,
     -66,    76,   -66,   -66,   -66,   239,   725,   141,    93,  -196,
      93,  -238,    77,   307,   508,   454,   726,   435,    20,   497,
     -74,  -114,   -35,    72,   436,   -77,  -170,  -118,   -35,  -118,
     705,    43,  -163,   437,   558,   209,    44,    74,    75,   -66,
     -66,    78,   -66,    76,   305,   727,    79,   151,   306,  -184,
    -209,    73,   572,   -77,   438,   -66,   -66,   317,   -66,  -238,
      45,   789,   370,   201,    74,    75,   573,   -66,   -66,   -66,
      76,   -66,   -66,   -66,   560,   790,   275,   371,  -209,   895,
    -238,    77,   307,   439,   276,  -114,   679,   791,   440,    80,
      17,   169,     2,   -35,   497,   437,  -227,   972,   372,    74,
      75,   792,  -122,   373,  -122,    76,   666,   973,   -66,   -66,
      78,   -66,   170,   436,   -66,    79,   151,   -66,   -66,   124,
     -66,  -249,   437,   793,   -79,   795,    74,    75,   125,   -66,
     -66,   -66,    76,   -66,   -66,   -66,   974,   794,   561,   796,
     947,   282,  -249,   438,  -249,   439,   667,  -249,   164,   219,
     440,    80,   -79,   359,   948,  1118,   220,  -451,   629,   237,
    -227,    74,    75,   628,  -451,   221,   360,    76,   895,  1119,
     -66,   -66,   439,   -66,   709,   679,   -66,   440,   151,   -66,
     -66,   -66,   -66,   -66,   437,  -451,   222,  1122,    74,    75,
    -451,   -66,   -66,   -66,    76,   -66,   -66,   -66,   597,   712,
    1216,  1123,   661,   767,   -66,   598,   -66,    78,   667,   -66,
     768,   319,    79,    80,  1217,   601,   985,   662,   429,   340,
     223,   604,   602,    74,    75,   713,   169,   430,   605,    76,
     916,   616,   -66,   -66,   439,   -66,  -199,   436,   663,   440,
     151,   -66,   -66,   664,   -66,  -249,   437,   170,   665,   307,
      74,    75,   617,   -66,   -66,   -66,    76,   -66,   -66,   -66,
     606,   607,   619,   609,  -199,   742,  -249,   438,   307,   242,
     667,   986,    20,   -70,   343,    80,   -77,  -170,   686,   -70,
     432,   489,    43,  -163,   817,    60,  -121,    44,    20,   433,
     490,  -121,   818,  -121,   -66,   -66,   439,   -66,   666,   616,
      23,   440,   151,    22,   -77,   436,   -66,   488,   753,   -66,
     -66,   136,   -66,  -249,   437,  1259,    23,  1262,    74,    75,
     617,   -66,   -66,   -66,    76,   -66,   -66,   -66,   803,  1260,
     619,  1263,   907,  1266,  -249,   438,  -249,   804,   667,   908,
     332,   178,   555,   687,   -70,   688,   333,  1267,   437,  -237,
     556,   782,    74,    75,   637,   799,  -237,   371,    76,   641,
    1106,   638,   -66,   -66,   439,   -66,   642,  1107,   -66,   440,
     151,   -66,   -66,   754,  1208,  -386,  1108,  -237,   372,  -237,
      74,    75,  -237,   -66,   -66,   -66,    76,   -66,   -66,   -66,
    1109,   646,   647,   759,   649,   163,  -386,  1110,  -447,   745,
     667,  -386,   164,   440,    80,   751,   185,   746,   186,  -447,
    -447,   802,   644,   752,   543,    74,    75,   -93,  -172,   645,
     543,    76,   338,    43,   -66,   -66,   439,   -66,    44,   339,
     -66,  1209,   151,   -66,   -66,   544,   -66,  -435,   340,   760,
    -433,   544,    74,    75,   569,   -66,   -66,   -66,    76,   -66,
     -66,   -66,   146,   731,  1104,   830,   831,   288,  -435,   341,
     507,  1027,   514,  -435,   289,   219,    79,    80,   567,   930,
     852,   853,   220,  -450,   568,   931,   603,    74,    75,   608,
    -450,   221,   643,    76,   907,   648,   -66,   -66,   342,   -66,
     828,   908,   -66,   343,   151,   -66,   -66,   -66,   -66,   -66,
     437,  -450,   222,   542,    74,    75,  -450,   -66,   -66,   -66,
      76,   -66,   -66,   -66,   829,   912,   913,   914,   543,    32,
     -66,    33,   -66,   755,   667,   -66,   886,   271,    79,    80,
     506,  -432,   507,   861,   887,   272,   223,   862,  -432,   544,
    -170,   683,   169,   881,   545,    43,   149,   892,   -66,   -66,
      44,   -66,   893,    73,   -66,   440,   151,   -66,   -66,  -432,
     -66,  -238,   684,   170,  -432,  -236,    74,    75,  -236,   -66,
     -66,   -66,    76,   -66,   -66,   -66,   863,   864,   282,   987,
     905,   906,  -238,    77,  -238,   164,   -66,  -238,   469,   -66,
     -66,   -66,   -66,   -66,   616,   293,   294,   295,    74,    75,
     172,   -66,   -66,   -66,    76,   -66,   -66,   -66,   273,   940,
     -66,   -66,    78,   -66,   -66,   617,   -66,    79,   151,   -66,
    1039,  1024,   509,   559,   510,   619,   173,   174,  1040,   765,
     766,  -454,   848,  1031,   988,   954,  1036,  1032,   371,  1033,
     849,  1041,   -66,   -66,    78,   -66,   149,   662,  1042,    79,
     151,  1052,  1053,    73,   -66,   488,   955,   -66,   -66,   372,
     -66,  -238,  1117,  1058,  -454,  1061,    74,    75,   663,   -66,
     -66,   -66,    76,   -66,   -66,   -66,  1054,  1124,   665,   756,
    1055,  1125,  -238,    77,  -238,  1126,   526,   -66,  1127,  1228,
     -66,   -66,  1229,   -66,   -66,   340,   772,   773,   774,    74,
      75,   835,   -66,   -66,   -66,    76,   -66,   -66,   -66,  1230,
     -66,   -66,    78,   -66,  1231,   -66,   616,    79,   151,   514,
     -66,   922,  1232,  -172,  1236,  1233,  1243,  1244,    43,  1255,
    1256,  1261,  1237,    44,  1268,  1269,   683,   617,  1270,  1223,
    1271,   733,   836,   -66,   -66,   342,   -66,   619,   734,   -66,
     343,   151,   -66,   -66,  1272,   941,  -350,   684,  1273,   307,
    1224,    74,    75,  1274,   -66,   -66,   -66,    76,   -66,   -66,
     -66,   735,    18,   907,  1275,  1276,    61,  -350,   736,   132,
     908,  -314,  -350,   476,  -314,  -314,  -314,  -314,  -314,   437,
     253,   467,   505,    74,    75,   871,  -314,  -314,  -314,    76,
    -314,  -314,  -314,    34,   466,   -66,   -66,    78,   -66,  -314,
     662,  -314,   942,   151,  -314,   457,   -90,  -170,   315,  1030,
     919,   105,    43,  -163,   212,   577,   277,    44,   810,  1062,
     335,   663,   976,   613,   278,   288,   872,  -314,  -314,     0,
    -314,   665,   289,  -260,   440,    80,  -260,  -260,  -260,  -260,
    -260,   146,   173,   174,   600,    74,    75,     0,  -260,  -260,
    -260,    76,  -260,  -260,  -260,     0,     0,   288,  1005,     0,
       0,  -260,     0,  -260,   289,   -66,  -260,     0,   -66,   -66,
     -66,   -66,   -66,   662,     0,     0,   546,    74,    75,     0,
     -66,   -66,   -66,    76,   -66,   -66,   -66,  1007,     0,  -260,
    -260,   543,  -260,   -66,   663,   -66,    79,    80,   -66,  -584,
     620,     0,   662,   682,   665,     0,     0,   621,     0,     0,
       0,   409,   544,  1006,     0,  -664,   410,   547,   683,     0,
       0,   -66,   -66,   663,   -66,     0,     0,     0,    79,   151,
       0,     0,     0,   665,     0,     0,  -664,   411,     0,   684,
       0,  -664,  1008,     0,   685,   868,  -664,   412,   413,   414,
     415,   416,   417,   418,   419,   530,   420,   421,   422,   423,
     424,   767,     0,  -434,     0,     0,     0,     0,   768,   -66,
    -434,   622,   -66,   -66,     0,   -66,   -66,   340,     0,     0,
       0,    74,    75,   778,   -66,   -66,   -66,    76,   -66,   -66,
     -66,  -434,     0,   178,     0,     0,  -434,   -66,   543,     0,
     559,   514,   -66,     0,   179,   180,     0,   181,  -452,     0,
       0,     0,     0,     0,     0,  -452,   182,   183,   184,   544,
     531,     0,   532,   767,   779,   -66,   -66,     0,   -66,     0,
     768,  -326,   343,   151,  -326,  -326,  -452,  -326,  -326,   340,
       0,  -452,     0,    74,    75,     0,  -326,  -326,  -326,    76,
    -326,  -326,  -326,     0,     0,   895,     0,   536,   185,  -326,
     186,     0,   679,  -288,  -326,   744,  -288,  -288,  -288,  -288,
    -288,   437,     0,     0,     0,    74,    75,     0,  -288,  -288,
    -288,    76,     0,   537,   538,     0,     0,  -326,  -326,     0,
    -326,  -288,   282,  -288,   343,    80,  -288,     0,     0,   164,
    -274,     0,     0,  -274,  -274,  -274,  -274,  -274,     0,     0,
       0,     0,    74,    75,     0,  -274,  -274,  -274,    76,  -288,
    -288,   439,  -288,     0,   756,     0,   440,    80,  -274,     0,
    -274,   526,  -302,  -274,     0,  -302,  -302,     0,  -302,  -302,
     340,     0,     0,   749,    74,    75,   666,  -302,  -302,  -302,
      76,   750,     0,   436,  -241,     0,  -274,  -274,    78,  -274,
    -302,  -241,   437,    79,    80,  -302,    74,    75,     0,   537,
     538,     0,    76,     0,     0,     0,     0,     0,  1106,     0,
       0,     0,  -241,   438,  -241,  1107,  -360,  -241,  -302,  -302,
     342,  -302,  1128,  -360,  1108,   343,    80,     0,    74,    75,
    1129,     0,     0,   692,    76,  1130,     0,   616,  1109,     0,
       0,   885,   439,  1131,  -360,  1110,  1106,   440,    80,  -360,
     616,     0,     0,  1107,  -359,     0,     0,     0,   617,   693,
     694,  -359,  1108,     0,     0,     0,    74,    75,   619,     0,
     149,   617,    76,     0,   439,     0,  1109,    73,  -230,  1111,
      80,   619,  -359,  1110,     0,  -230,     0,  -359,   780,     0,
      74,    75,     0,     0,   338,     0,    76,     0,     0,     0,
       0,   339,  -428,   543,     0,     0,  -230,    77,  -230,  -428,
     340,  -230,   439,   686,    74,    75,     0,  1111,    80,   890,
      76,  -248,     0,   953,   544,     0,     0,   891,  -248,   781,
    -428,   341,   338,     0,     0,  -428,    78,     0,   954,   339,
    -427,    79,    80,     0,     0,   693,   694,  -427,   340,  -248,
       0,  -248,    74,    75,  -248,   733,     0,     0,    76,   955,
     342,     0,   734,  -331,   956,   343,    80,     0,  -427,   341,
    -331,    19,     0,  -427,    20,    74,    75,     0,   687,   733,
     688,    76,     0,     0,     0,   735,   734,  -330,    21,    22,
       0,  -331,   736,     0,  -330,     0,  -331,     0,   342,    74,
      75,     0,    23,   343,    80,    76,     0,     0,     0,   735,
       0,     0,  1106,     0,     0,  -330,   736,     0,  -225,  1107,
    -330,    78,   559,     0,     0,     0,   737,    80,  1108,     0,
    -453,   815,    74,    75,   313,     0,   700,   371,    76,   816,
     201,    73,  1109,   436,     0,    78,   616,     0,     0,  1110,
     737,    80,   437,     0,    74,    75,    74,    75,  -453,   338,
      76,     0,    76,  -453,     0,  -419,   339,   617,   202,     0,
     202,    77,  -553,   438,     0,   340,     0,   619,   439,    74,
      75,     0,     0,  1111,    80,    76,  -553,   279,     0,     0,
       0,     0,     0,     0,     0,   280,   341,   338,   179,   180,
      78,   181,   439,  -418,   339,    79,    80,   440,    80,     0,
     182,   183,   184,   340,     0,     0,     0,    74,    75,     0,
     666,     0,   338,    76,     0,   342,   -98,   436,  -423,   339,
     343,    80,     0,     0,   341,     0,   437,     0,   340,     0,
      74,    75,    74,    75,   338,     0,    76,     0,    76,     0,
    -422,   339,   185,     0,   186,     0,     0,   438,     0,   341,
     340,  1222,     0,   342,    74,    75,     0,     0,   343,    80,
      76,     0,     0,     0,     0,     0,  1223,     0,     0,     0,
     666,   341,     0,  1106,     0,     0,   439,   436,   342,   488,
    1107,   440,    80,   343,    80,     0,   437,  1224,   338,  1108,
      74,    75,  1225,    74,    75,   339,    76,     0,     0,    76,
     342,     0,  1226,  1109,   340,   343,    80,   438,    74,    75,
    1110,   149,     0,     0,    76,     0,     0,  1223,    73,     0,
     488,     0,     0,     0,     0,   341,   149,     0,     0,     0,
       0,    74,    75,    73,     0,     0,   439,    76,  1224,   439,
       0,   440,    80,  1227,  1111,    80,    74,    75,    77,   666,
       0,     0,    76,  1144,   342,     0,   436,     0,     0,   343,
      80,  1145,     0,    77,   733,   437,     0,     0,   616,    74,
      75,   734,     0,   178,     0,    76,     0,    78,     0,     0,
       0,  -337,    79,    80,    74,    75,   438,     0,  -337,   617,
      76,     0,    78,   530,   735,     0,   579,    79,    80,   619,
       0,   736,  -512,   580,   179,   180,     0,   181,  -551,  -337,
       0,  -578,   386,     0,  -337,   439,   182,   183,   184,     0,
     440,    80,     0,     0,     0,     0,     0,     0,     0,   581,
      78,     0,  -578,   387,     0,   737,    80,  -578,   185,     0,
     186,  -505,  -578,   388,   389,   390,   391,   392,   393,   394,
     395,     0,   396,   397,   398,   399,   400,   620,   531,     0,
     532,     0,     0,     0,   621,  -664,     0,   401,   409,     0,
       0,     0,  -664,   841,     0,     0,     0,     0,     0,     0,
       0,     0,   686,     0,   620,     0,     0,     0,     0,     0,
    -366,   621,  -664,  -664,   411,   409,     0,  -366,  -664,  -664,
     410,     0,     0,  -664,   412,   413,   414,   415,   416,   417,
     418,   419,  -664,   420,   421,   422,   423,   424,  -366,     0,
    -664,   411,     0,  -366,     0,  -664,     0,     0,   842,     0,
    -664,   412,   413,   414,   415,   416,   417,   418,   419,  -664,
     420,   421,   422,   423,   424,   626,     0,   687,     0,   688,
       0,     0,   408,  -629,     0,   622,   409,     0,     0,     0,
    -629,   410,     0,     0,     0,     0,     0,     0,     0,     0,
     755,     0,   626,     0,     0,     0,     0,     0,  -431,   408,
    -628,  -629,   411,   409,     0,   543,  -629,  -628,   410,     0,
       0,  -629,   412,   413,   414,   415,   416,   417,   418,   419,
    -629,   420,   421,   422,   423,   424,   544,     0,  -628,   411,
       0,  -431,     0,  -628,     0,     0,   425,     0,  -628,   412,
     413,   414,   415,   416,   417,   418,   419,  -628,   420,   421,
     422,   423,   424,   626,     0,     0,     0,   755,     0,     0,
     408,  -617,     0,   425,   409,  -429,     0,     0,  -617,   410,
       0,     0,  -429,     0,     0,     0,     0,     0,     0,     0,
     626,     0,     0,     0,     0,     0,     0,   408,  -615,  -617,
     411,   409,     0,  -429,  -617,  -615,   410,     0,  -429,  -617,
     412,   413,   414,   415,   416,   417,   418,   419,  -617,   420,
     421,   422,   423,   424,     0,     0,  -615,   411,     0,     0,
       0,  -615,     0,     0,   425,     0,  -615,   412,   413,   414,
     415,   416,   417,   418,   419,  -615,   420,   421,   422,   423,
     424,   626,     0,     0,     0,   755,     0,     0,   408,  -609,
       0,   425,   409,  -430,     0,     0,  -609,   410,     0,     0,
     543,     0,     0,     0,     0,     0,     0,     0,   626,     0,
       0,     0,     0,     0,     0,   408,  -607,  -609,   411,   409,
       0,  -430,  -609,  -607,   410,     0,  -430,  -609,   412,   413,
     414,   415,   416,   417,   418,   419,  -609,   420,   421,   422,
     423,   424,     0,     0,  -607,   411,     0,     0,     0,  -607,
       0,     0,   425,     0,  -607,   412,   413,   414,   415,   416,
     417,   418,   419,  -607,   420,   421,   422,   423,   424,   626,
       0,     0,     0,  1037,     0,     0,   408,  -616,     0,   425,
     409,  1038,     0,     0,  -616,   410,     0,     0,   954,     0,
       0,     0,     0,     0,     0,     0,   626,     0,     0,     0,
       0,     0,     0,   408,  -613,  -616,   411,   409,     0,   955,
    -616,  -613,   410,     0,  -336,  -616,   412,   413,   414,   415,
     416,   417,   418,   419,  -616,   420,   421,   422,   423,   424,
       0,     0,  -613,   411,     0,     0,     0,  -613,     0,     0,
     425,     0,  -613,   412,   413,   414,   415,   416,   417,   418,
     419,  -613,   420,   421,   422,   423,   424,   626,     0,     0,
       0,   953,     0,     0,   408,  -608,     0,   425,   409,  -335,
       0,     0,  -608,   410,     0,     0,  -335,     0,     0,     0,
       0,     0,     0,     0,   626,     0,     0,     0,     0,     0,
       0,   408,  -605,  -608,   411,   409,     0,  -335,  -608,  -605,
     410,     0,  -335,  -608,   412,   413,   414,   415,   416,   417,
     418,   419,  -608,   420,   421,   422,   423,   424,     0,     0,
    -605,   411,     0,     0,     0,  -605,     0,     0,   425,     0,
    -605,   412,   413,   414,   415,   416,   417,   418,   419,  -605,
     420,   421,   422,   423,   424,   626,     0,     0,     0,   953,
       0,     0,   408,  -601,     0,   425,   409,  -334,     0,     0,
    -601,   410,     0,     0,   954,     0,     0,     0,     0,     0,
       0,     0,   626,     0,     0,     0,     0,     0,     0,   408,
    -599,  -601,   411,   409,     0,   955,  -601,  -599,   410,     0,
    -334,  -601,   412,   413,   414,   415,   416,   417,   418,   419,
    -601,   420,   421,   422,   423,   424,     0,     0,  -599,   411,
       0,     0,     0,  -599,     0,     0,   425,     0,  -599,   412,
     413,   414,   415,   416,   417,   418,   419,  -599,   420,   421,
     422,   423,   424,   626,     0,     0,     0,   953,     0,     0,
     408,  -600,     0,   425,   409,  -332,     0,     0,  -600,   410,
       0,     0,  -332,     0,     0,     0,     0,     0,     0,     0,
     626,     0,     0,     0,     0,     0,     0,   408,  -597,  -600,
     411,   409,     0,  -332,  -600,  -597,   410,     0,  -332,  -600,
     412,   413,   414,   415,   416,   417,   418,   419,  -600,   420,
     421,   422,   423,   424,     0,     0,  -597,   411,     0,     0,
       0,  -597,     0,     0,   425,     0,  -597,   412,   413,   414,
     415,   416,   417,   418,   419,  -597,   420,   421,   422,   423,
     424,   626,     0,     0,     0,   953,     0,     0,   408,  -625,
       0,   425,   409,  -333,     0,     0,  -625,   410,     0,     0,
     954,     0,     0,     0,     0,     0,     0,     0,   626,     0,
       0,     0,     0,     0,     0,   408,  -623,  -625,   411,   409,
       0,  -333,  -625,  -623,   410,     0,  -333,  -625,   412,   413,
     414,   415,   416,   417,   418,   419,  -625,   420,   421,   422,
     423,   424,     0,     0,  -623,   411,     0,     0,     0,  -623,
       0,     0,   425,     0,  -623,   412,   413,   414,   415,   416,
     417,   418,   419,  -623,   420,   421,   422,   423,   424,   626,
       0,     0,     0,  1234,     0,     0,   408,  -624,     0,   425,
     409,  1235,     0,     0,  -624,   410,     0,     0,  1223,     0,
       0,     0,     0,     0,     0,     0,   626,     0,     0,     0,
       0,     0,     0,   408,  -621,  -624,   411,   409,     0,  1224,
    -624,  -621,   410,     0,  -365,  -624,   412,   413,   414,   415,
     416,   417,   418,   419,  -624,   420,   421,   422,   423,   424,
       0,     0,  -621,   411,     0,     0,     0,  -621,     0,     0,
     425,     0,  -621,   412,   413,   414,   415,   416,   417,   418,
     419,  -621,   420,   421,   422,   423,   424,   620,     0,     0,
       0,     0,     0,  -590,   621,     0,  1132,   425,   409,     0,
       0,     0,  -664,   410,  1133,     0,     0,     0,     0,     0,
       0,   616,  1245,     0,   579,     0,     0,     0,     0,     0,
    -364,   580,  -578,  -664,   411,     0,     0,  -364,  -664,  -578,
     811,     0,   617,  -664,   412,   413,   414,   415,   416,   417,
     418,   419,   619,   420,   421,   422,   423,   424,  -364,     0,
    -578,   387,     0,  -364,     0,  -578,     0,     0,   622,     0,
    -578,   388,   389,   390,   391,   392,   393,   394,   395,  -578,
     396,   397,   398,   399,   400,   579,     0,     0,     0,   281,
       0,     0,   580,  -578,     0,   812,     0,  -235,     0,     0,
    -578,   386,     0,     0,  -235,     0,     0,     0,     0,     0,
       0,     0,     0,   579,     0,     0,     0,     0,     0,     0,
     580,  -578,   387,     0,     0,  -235,  -578,  -235,  -578,   386,
    -235,  -578,   388,   389,   390,   391,   392,   393,   394,   395,
    -578,   396,   397,   398,   399,   400,   581,     0,     0,  -578,
     387,     0,     0,     0,  -578,     0,   401,     0,  -505,  -578,
     388,   389,   390,   391,   392,   393,   394,   395,  1134,   396,
     397,   398,   399,   400,   587,     0,  1135,  -385,     0,     0,
       0,   385,  -548,   616,   401,  -385,     0,     0,     0,  -548,
     386,     0,  -385,     0,     0,     0,     0,     0,     0,     0,
       0,   587,     0,     0,   617,     0,     0,     0,   385,  -547,
    -548,   387,     0,  -385,   619,  -548,  -547,   386,  -385,     0,
    -548,   388,   389,   390,   391,   392,   393,   394,   395,  -548,
     396,   397,   398,   399,   400,     0,     0,  -547,   387,     0,
       0,     0,  -547,     0,     0,   401,     0,  -547,   388,   389,
     390,   391,   392,   393,   394,   395,  -547,   396,   397,   398,
     399,   400,   587,     0,     0,  1245,  1245,     0,     0,   385,
    -536,     0,   401,  -363,  -361,     0,     0,  -536,   386,     0,
    1223,  -361,     0,     0,     0,     0,     0,     0,     0,   587,
       0,     0,     0,     0,     0,     0,   385,  -534,  -536,   387,
       0,  1224,  -361,  -536,  -534,   386,  -363,  -361,  -536,   388,
     389,   390,   391,   392,   393,   394,   395,  -536,   396,   397,
     398,   399,   400,     0,     0,  -534,   387,     0,     0,     0,
    -534,     0,     0,   401,     0,  -534,   388,   389,   390,   391,
     392,   393,   394,   395,  -534,   396,   397,   398,   399,   400,
     587,     0,     0,  1245,     0,     0,     0,   385,  -528,     0,
     401,  -362,     0,     0,     0,  -528,   386,     0,  1223,     0,
       0,     0,     0,     0,     0,     0,     0,   587,     0,     0,
       0,     0,     0,     0,   385,  -526,  -528,   387,     0,  -362,
       0,  -528,  -526,   386,  -362,     0,  -528,   388,   389,   390,
     391,   392,   393,   394,   395,  -528,   396,   397,   398,   399,
     400,     0,     0,  -526,   387,     0,     0,     0,  -526,     0,
       0,   401,     0,  -526,   388,   389,   390,   391,   392,   393,
     394,   395,  -526,   396,   397,   398,   399,   400,   587,     0,
       0,     0,     0,     0,     0,   385,  -535,     0,   401,     0,
       0,     0,     0,  -535,   386,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   587,     0,     0,     0,     0,
       0,     0,   385,  -532,  -535,   387,     0,     0,     0,  -535,
    -532,   386,     0,     0,  -535,   388,   389,   390,   391,   392,
     393,   394,   395,  -535,   396,   397,   398,   399,   400,     0,
       0,  -532,   387,     0,     0,     0,  -532,     0,     0,   401,
       0,  -532,   388,   389,   390,   391,   392,   393,   394,   395,
    -532,   396,   397,   398,   399,   400,   587,     0,     0,     0,
       0,     0,     0,   385,  -527,     0,   401,     0,     0,     0,
       0,  -527,   386,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   587,     0,     0,     0,     0,     0,     0,
     385,  -524,  -527,   387,     0,     0,     0,  -527,  -524,   386,
       0,     0,  -527,   388,   389,   390,   391,   392,   393,   394,
     395,  -527,   396,   397,   398,   399,   400,     0,     0,  -524,
     387,     0,     0,     0,  -524,     0,     0,   401,     0,  -524,
     388,   389,   390,   391,   392,   393,   394,   395,  -524,   396,
     397,   398,   399,   400,   587,     0,     0,     0,     0,     0,
       0,   385,  -520,     0,   401,     0,     0,     0,     0,  -520,
     386,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   587,     0,     0,     0,     0,     0,     0,   385,  -518,
    -520,   387,     0,     0,     0,  -520,  -518,   386,     0,     0,
    -520,   388,   389,   390,   391,   392,   393,   394,   395,  -520,
     396,   397,   398,   399,   400,     0,     0,  -518,   387,     0,
       0,     0,  -518,     0,     0,   401,     0,  -518,   388,   389,
     390,   391,   392,   393,   394,   395,  -518,   396,   397,   398,
     399,   400,   587,     0,     0,     0,     0,     0,     0,   385,
    -519,     0,   401,     0,     0,     0,     0,  -519,   386,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   587,
       0,     0,     0,     0,     0,     0,   385,  -516,  -519,   387,
       0,     0,     0,  -519,  -516,   386,     0,     0,  -519,   388,
     389,   390,   391,   392,   393,   394,   395,  -519,   396,   397,
     398,   399,   400,     0,     0,  -516,   387,     0,     0,     0,
    -516,     0,     0,   401,     0,  -516,   388,   389,   390,   391,
     392,   393,   394,   395,  -516,   396,   397,   398,   399,   400,
     587,     0,     0,     0,     0,     0,     0,   385,  -544,     0,
     401,     0,     0,     0,     0,  -544,   386,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   587,     0,     0,
       0,     0,     0,     0,   385,  -542,  -544,   387,     0,     0,
       0,  -544,  -542,   386,     0,     0,  -544,   388,   389,   390,
     391,   392,   393,   394,   395,  -544,   396,   397,   398,   399,
     400,     0,     0,  -542,   387,     0,     0,     0,  -542,     0,
       0,   401,     0,  -542,   388,   389,   390,   391,   392,   393,
     394,   395,  -542,   396,   397,   398,   399,   400,   587,     0,
       0,     0,     0,     0,     0,   385,  -543,     0,   401,     0,
       0,     0,     0,  -543,   386,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   587,     0,     0,     0,     0,
       0,     0,   385,  -540,  -543,   387,     0,     0,     0,  -543,
    -540,   386,     0,     0,  -543,   388,   389,   390,   391,   392,
     393,   394,   395,  -543,   396,   397,   398,   399,   400,     0,
       0,  -540,   387,     0,     0,     0,  -540,     0,     0,   401,
       0,  -540,   388,   389,   390,   391,   392,   393,   394,   395,
    -540,   396,   397,   398,   399,   400,   626,   530,     0,     0,
       0,     0,     0,   408,     0,   743,   401,   409,   179,   180,
       0,   181,   410,     0,     0,     0,     0,     0,     0,     0,
     182,   183,   184,   652,     0,     0,     0,   863,   864,   653,
     408,     0,     0,   411,   409,     0,     0,     0,     0,   410,
       0,     0,     0,   412,   413,   414,   415,   416,   417,   418,
     419,     0,   420,   421,   422,   423,   424,     0,     0,     0,
     411,     0,   531,     0,   532,     0,     0,   425,     0,     0,
     412,   413,   414,   415,   416,   417,   418,   419,   983,   420,
     421,   422,   423,   424,   626,     0,  -570,   686,     0,     0,
    -587,   408,     0,  -570,   425,   409,     0,     0,   179,   180,
     410,   181,     0,     0,     0,     0,     0,     0,     0,   626,
     182,   183,   184,     0,  -570,  -589,   408,   984,   611,     0,
     409,   411,     0,     0,  -570,   410,     0,     0,     0,     0,
       0,   412,   413,   414,   415,   416,   417,   418,   419,     0,
     420,   421,   422,   423,   424,     0,   411,     0,     0,     0,
       0,     0,   687,     0,   688,   425,   412,   413,   414,   415,
     416,   417,   418,   419,     0,   420,   421,   422,   423,   424,
     587,   747,     0,   281,     0,     0,     0,   385,     0,   748,
     425,  -234,   179,   180,     0,   181,   386,     0,   169,     0,
       0,     0,     0,     0,   182,   183,   184,   383,     0,     0,
       0,   830,   831,   384,   385,     0,     0,   387,     0,   170,
       0,  -234,     0,   386,  -234,     0,     0,   388,   389,   390,
     391,   392,   393,   394,   395,   821,   396,   397,   398,   399,
     400,     0,     0,  -552,   387,     0,   531,     0,   532,     0,
    -552,   401,     0,     0,   388,   389,   390,   391,   392,   393,
     394,   395,     0,   396,   397,   398,   399,   400,   407,     0,
       0,  -552,     0,     0,     0,   408,  -552,  1148,   401,   409,
       0,  -552,     0,     0,   410,  1149,     0,     0,     0,     0,
    -552,     0,   616,   612,     0,   281,     0,     0,     0,   384,
     385,     0,     0,  -232,     0,   411,     0,     0,     0,   386,
    -232,     0,     0,   617,     0,   412,   413,   414,   415,   416,
     417,   418,   419,   619,   420,   421,   422,   423,   424,     0,
     387,  -232,  -551,  -232,     0,     0,  -232,     0,     0,   425,
     388,   389,   390,   391,   392,   393,   394,   395,     0,   396,
     397,   398,   399,   400,   626,     0,     0,     0,     0,     0,
       0,   408,   -79,  1188,   401,   409,     0,     0,   235,  -144,
     410,  1189,     0,   236,     0,     0,     0,  -151,   662,   587,
       0,   281,     0,     0,     0,  -509,   385,     0,     0,  -233,
     -79,   411,     0,     0,     0,   386,   169,   237,     0,   663,
       0,   412,   413,   414,   415,   416,   417,   418,   419,   665,
     420,   421,   422,   423,   424,     0,   387,  -233,  -632,  -233,
       0,     0,  -233,     0,     0,   425,   388,   389,   390,   391,
     392,   393,   394,   395,  1003,   396,   397,   398,   399,   400,
     626,     0,  -656,     0,     0,     0,     0,   408,     0,  -656,
     401,   409,     0,     0,     0,     0,   843,     0,     0,     0,
       0,     0,     0,     0,     0,   587,     0,   882,   894,     0,
    -656,  -511,   385,  1004,   651,   883,  -246,   411,     0,     0,
    -656,   386,   683,  -246,     0,     0,     0,   412,   413,   414,
     415,   416,   417,   418,   419,     0,   420,   421,   422,   423,
     424,     0,   387,   684,  -246,  -247,  -246,     0,  -247,  -246,
       0,   844,   388,   389,   390,   391,   392,   393,   394,   395,
       0,   396,   397,   398,   399,   400,   587,     0,     0,   536,
     894,     0,     0,   385,     0,     0,   401,  -303,  -245,     0,
    -303,  -303,   386,  -303,  -303,   683,     0,     0,     0,     0,
       0,   587,  -303,  -303,  -303,   537,   538,     0,   385,     0,
       0,     0,     0,   387,     0,  -303,   684,   813,  -245,     0,
    -303,  -245,     0,   388,   389,   390,   391,   392,   393,   394,
     395,     0,   396,   397,   398,   399,   400,     0,   387,     0,
       0,     0,     0,  -303,  -303,     0,  -303,   401,   388,   389,
     390,   391,   392,   393,   394,   395,     0,   396,   397,   398,
     399,   400,   219,     0,     0,     0,     0,     0,   562,   220,
       0,     0,   814,  1136,     0,  1138,     0,     0,   221,     0,
       0,  1137,     0,  1139,     0,     0,     0,     0,   616,   175,
     616,     0,     0,     0,     0,  -445,     0,  -253,     0,   222,
    -253,  -253,  -253,  -253,  -253,   563,  -445,  -445,     0,   617,
       0,   617,  -253,  -253,  -253,  -253,  -253,   176,   177,   619,
       0,   619,     0,   175,   894,  -253,     0,  -253,     0,     0,
    -253,  -252,  -243,   223,  -252,  -252,  -252,  -252,  -252,  -243,
       0,     0,     0,     0,     0,     0,  -252,  -252,  -252,  -252,
    -252,   176,   177,  -253,  -253,   175,  -253,     0,     0,  -252,
    -243,  -252,  -243,  -251,  -252,  -243,  -251,  -251,  -251,  -251,
    -251,     0,     0,     0,     0,     0,     0,     0,  -251,  -251,
    -251,  -251,  -251,   176,   177,     0,     0,  -252,  -252,   175,
    -252,  -251,     0,  -251,     0,     0,  -251,  -250,     0,     0,
    -250,  -250,  -250,  -250,  -250,     0,     0,     0,     0,     0,
       0,     0,  -250,  -250,  -250,  -250,  -250,   176,   177,  -251,
    -251,   695,  -251,     0,     0,  -250,     0,  -250,     0,  -307,
    -250,     0,  -307,  -307,  -307,  -307,  -307,     0,     0,     0,
       0,     0,     0,     0,  -307,  -307,  -307,  -307,  -307,   696,
     697,     0,     0,  -250,  -250,   695,  -250,  -307,     0,  -307,
       0,     0,  -307,  -306,     0,     0,  -306,  -306,  -306,  -306,
    -306,     0,     0,     0,     0,     0,     0,     0,  -306,  -306,
    -306,  -306,  -306,   696,   697,  -307,  -307,   695,  -307,     0,
       0,  -306,     0,  -306,     0,  -305,  -306,     0,  -305,  -305,
    -305,  -305,  -305,     0,     0,     0,     0,     0,     0,     0,
    -305,  -305,  -305,  -305,  -305,   696,   697,     0,     0,  -306,
    -306,   695,  -306,  -305,     0,  -305,     0,     0,  -305,  -304,
       0,     0,  -304,  -304,  -304,  -304,  -304,     0,     0,     0,
       0,     0,     0,     0,  -304,  -304,  -304,  -304,  -304,   696,
     697,  -305,  -305,   528,  -305,     0,     0,  -304,     0,  -304,
       0,  -399,  -304,     0,  -399,  -399,     0,  -399,  -399,     0,
       0,     0,     0,     0,     0,     0,  -399,  -399,  -399,  -399,
    -399,  -399,  -399,     0,     0,  -304,  -304,   950,  -304,  -399,
       0,     0,     0,   529,  -399,  -341,     0,     0,  -388,  -388,
       0,  -388,  -341,     0,     0,     0,     0,     0,     0,     0,
    -388,  -388,  -388,  -388,  -388,  -388,  -388,  -399,  -399,     0,
    -399,  1219,     0,  -341,     0,     0,     0,   951,  -341,  -370,
       0,     0,  -393,  -393,     0,  -393,  -370,     0,     0,     0,
       0,     0,     0,     0,  -393,  -393,  -393,  -393,  -393,  -393,
    -393,  -388,  -388,     0,  -388,   172,   894,  -370,     0,     0,
       0,  1220,  -370,  -275,  -244,     0,  -275,  -275,  -275,  -275,
    -275,   683,     0,     0,     0,     0,     0,     0,  -275,  -275,
    -275,   173,   174,     0,     0,  -393,  -393,   172,  -393,     0,
       0,  -275,  -244,  -275,  -244,   273,  -275,  -244,  -275,  -275,
    -275,  -275,  -275,     0,     0,     0,     0,     0,     0,     0,
    -275,  -275,  -275,   173,   174,     0,     0,     0,     0,  -275,
    -275,   539,  -275,  -275,     0,  -275,     0,     0,  -275,  -319,
       0,     0,  -319,  -319,     0,  -319,  -319,     0,     0,     0,
       0,     0,     0,     0,  -319,  -319,  -319,  -319,  -319,   540,
     541,  -275,  -275,   692,  -275,     0,     0,  -319,     0,     0,
       0,  -289,  -319,     0,  -289,  -289,  -289,  -289,  -289,     0,
       0,     0,     0,     0,     0,     0,  -289,  -289,  -289,   693,
     694,     0,     0,     0,     0,  -319,  -319,   692,  -319,  -289,
       0,  -289,     0,     0,  -289,   885,     0,     0,  -289,  -289,
    -289,  -289,  -289,     0,     0,     0,     0,     0,     0,     0,
    -289,  -289,  -289,   693,   694,     0,     0,  -289,  -289,   539,
    -289,     0,     0,  -289,     0,  -289,     0,  -318,  -289,     0,
    -318,  -318,     0,  -318,  -318,     0,     0,     0,     0,     0,
       0,     0,  -318,  -318,  -318,  -318,  -318,   540,   541,     0,
       0,  -289,  -289,   539,  -289,  -318,     0,     0,     0,     0,
    -318,  -317,     0,     0,  -317,  -317,     0,  -317,  -317,     0,
       0,     0,     0,     0,     0,     0,  -317,  -317,  -317,  -317,
    -317,   540,   541,  -318,  -318,   539,  -318,     0,     0,  -317,
       0,     0,     0,  -316,  -317,     0,  -316,  -316,     0,  -316,
    -316,     0,     0,     0,     0,     0,     0,     0,  -316,  -316,
    -316,  -316,  -316,   540,   541,     0,     0,  -317,  -317,   188,
    -317,  -316,     0,     0,     0,     0,  -316,  -265,     0,     0,
    -265,  -265,  -265,  -265,  -265,     0,     0,     0,     0,     0,
       0,     0,  -265,  -265,  -265,     0,     0,     0,     0,  -316,
    -316,   188,  -316,     0,     0,  -265,     0,  -265,     0,  -264,
    -265,     0,  -264,  -264,  -264,  -264,  -264,     0,     0,     0,
       0,     0,     0,     0,  -264,  -264,  -264,     0,     0,     0,
       0,     0,     0,   189,  -265,   188,  -265,  -264,     0,  -264,
       0,     0,  -264,  -262,     0,     0,  -262,  -262,  -262,  -262,
    -262,     0,     0,     0,     0,     0,     0,     0,  -262,  -262,
    -262,     0,     0,     0,     0,   189,  -264,   188,  -264,     0,
       0,  -262,     0,  -262,     0,  -263,  -262,     0,  -263,  -263,
    -263,  -263,  -263,     0,     0,     0,     0,     0,     0,     0,
    -263,  -263,  -263,     0,     0,     0,     0,     0,     0,   189,
    -262,   690,  -262,  -263,     0,  -263,     0,     0,  -263,  -279,
       0,     0,  -279,  -279,  -279,  -279,  -279,     0,     0,     0,
       0,     0,     0,     0,  -279,  -279,  -279,     0,     0,     0,
       0,   189,  -263,   536,  -263,     0,     0,  -279,   686,  -279,
       0,   744,  -279,     0,  -303,  -303,   884,  -303,  -303,   179,
     180,     0,   181,     0,     0,     0,  -303,  -303,  -303,   537,
     538,   182,   183,   184,   950,   691,  -279,     0,  -279,  -303,
       0,   690,  -388,     0,  -303,  -388,  -388,     0,  -388,  -278,
       0,     0,  -278,  -278,  -278,  -278,  -278,  -388,  -388,  -388,
    -388,  -388,  -388,  -388,  -278,  -278,  -278,  -303,  -303,     0,
    -303,     0,   888,   687,   951,   688,     0,  -278,     0,  -278,
     889,     0,  -278,   179,   180,     0,   181,     0,     0,     0,
       0,     0,     0,     0,     0,   182,   183,   184,  -388,  -388,
       0,  -388,   690,     0,     0,   691,  -278,     0,  -278,     0,
    -276,     0,     0,  -276,  -276,  -276,  -276,  -276,     0,     0,
       0,   690,     0,     0,     0,  -276,  -276,  -276,     0,  -277,
       0,     0,  -277,  -277,  -277,  -277,  -277,   687,  -276,   688,
    -276,  1140,     0,  -276,  -277,  -277,  -277,     0,     0,  1141,
       0,     0,     0,     0,     0,     0,   616,  -277,     0,  -277,
       0,     0,  -277,  1142,     0,     0,   691,  -276,  1219,  -276,
       0,  1143,     0,     0,     0,     0,  -393,   617,   616,  -393,
    -393,     0,  -393,     0,     0,   691,  -277,   619,  -277,     0,
     534,  -393,  -393,  -393,  -393,  -393,  -393,  -393,  -293,   617,
       0,  -293,  -293,     0,  -293,  -293,     0,     0,  1220,   619,
       0,     0,     0,  -293,  -293,  -293,     0,     0,     0,     0,
       0,     0,  1146,     0,     0,     0,  -293,     0,   534,     0,
    1147,  -293,  -393,  -393,     0,  -393,  -292,   616,     0,  -292,
    -292,     0,  -292,  -292,     0,     0,     0,     0,   534,     0,
       0,  -292,  -292,  -292,   535,  -293,  -290,  -293,   617,  -290,
    -290,     0,  -290,  -290,  -292,     0,     0,     0,   619,  -292,
       0,  -290,  -290,  -290,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,  -290,     0,   534,     0,     0,  -290,
       0,     0,   535,  -292,  -291,  -292,     0,  -291,  -291,     0,
    -291,  -291,     0,     0,     0,     0,   277,     0,     0,  -291,
    -291,  -291,   535,  -290,   278,  -290,     0,  -275,  -275,     0,
    -275,     0,  -291,     0,     0,     0,     0,  -291,     0,  -275,
    -275,  -275,   173,   174,   749,     0,     0,     0,     0,     0,
       0,     0,   750,     0,     0,  -303,  -303,     0,  -303,     0,
     535,  -291,     0,  -291,   890,     0,     0,  -303,  -303,  -303,
     537,   538,   891,     0,     0,  -289,  -289,     0,  -289,     0,
    -275,  -275,     0,  -275,   999,     0,   650,  -289,  -289,  -289,
     693,   694,  -656,     0,  -656,     0,   845,   979,   845,  -656,
       0,  -656,     0,     0,     0,  -570,     0,     0,  -303,  -303,
       0,  -303,  -570,     0,     0,     0,     0,     0,     0,     0,
    -656,     0,  -656,  1000,   651,  -656,   651,  -656,  -289,  -289,
    -656,  -289,  -656,  -570,   610,     0,   980,   611,  -570,  -656,
       0,  -656,  -570,  -570,     0,   650,   821,   821,     0,  -570,
       0,     0,  -570,  -656,  -555,  -556,     0,     0,   821,     0,
    -656,  -555,  -556,     0,     0,     0,  -557,     0,     0,   821,
    -570,     0,     0,  -557,   611,  -570,     0,  -558,     0,     0,
    -570,  -656,  -555,  -556,  -558,   651,  -656,  -555,  -556,  -570,
       0,  -656,  -555,  -556,  -557,     0,     0,     0,     0,  -557,
    -656,  -555,  -556,   821,  -557,  -558,   821,     0,     0,     0,
    -558,  -559,     0,  -557,  -560,  -558,     0,     0,  -559,   846,
       0,  -560,     0,   854,  -558,     0,     0,   847,     0,     0,
       0,  -633,     0,     0,   662,   854,     0,     0,  -633,  -559,
       0,     0,  -560,  -636,  -559,     0,     0,  -560,   854,  -559,
    -636,     0,  -560,     0,     0,   663,  -637,     0,  -559,  -633,
    -634,  -560,     0,  -637,  -633,   665,     0,     0,     0,  -633,
       0,  -636,   854,     0,  -634,     0,  -636,     0,  -633,     0,
    -638,  -636,     0,   854,  -637,   854,     0,  -638,     0,  -637,
    -636,  -639,     0,  -640,  -637,     0,   854,     0,  -639,     0,
    -640,     0,     0,  -637,  -641,     0,     0,   821,  -638,     0,
       0,  -641,     0,  -638,     0,  -551,     0,     0,  -638,  -639,
     821,  -640,   616,     0,  -639,     0,  -640,  -638,  -549,  -639,
       0,  -640,  -641,     0,     0,  -549,     0,  -641,  -639,     0,
    -640,     0,  -641,   617,   821,     0,     0,     0,  -551,     0,
     821,  -641,  -550,   619,     0,     0,  -549,     0,  -554,   616,
       0,  -549,  -551,     0,     0,   616,  -549,     0,  1005,     0,
       0,     0,     0,     0,   854,  -549,  -654,     0,     0,     0,
    -550,     0,  -651,   662,     0,  -550,   617,     0,     0,  -651,
    -550,  -554,   854,     0,     0,     0,   619,     0,   854,  -550,
    -652,     0,     0,     0,   663,  -554,  -653,  -652,     0,  -654,
    -651,     0,     0,  -653,   665,  -651,   854,     0,     0,     0,
    -651,     0,   854,  1006,  -632,     0,     0,     0,  -652,  -651,
    -630,   662,     0,  -652,  -653,     0,     0,  -630,  -652,  -653,
     854,     0,     0,     0,  -653,     0,   854,  -652,  -631,     0,
       0,     0,   663,  -653,  -635,   662,     0,  -632,  -630,     0,
       0,   662,   665,  -630,  1184,     0,     0,     0,  -630,     0,
    1150,  -632,  1185,     0,     0,  1152,  -631,  -630,  1151,   662,
       0,  -631,   663,  1153,     0,   616,  -631,  -635,  1154,  1156,
     616,     0,   665,     0,  1158,  -631,  1155,  1157,     0,     0,
     663,  -635,  1159,   616,   616,  -632,   617,  1160,     0,   616,
     665,   617,  1162,     0,     0,  1161,   619,     0,  1164,  -632,
    1163,   619,   616,  1166,   617,   617,  1165,   616,     0,  1168,
     617,  1167,     0,   616,   619,   619,     0,  1169,   616,     0,
     619,  1170,  1172,   617,   662,     0,     0,  1174,   617,  1171,
    1173,     0,     0,   619,   617,  1175,   662,   662,   619,   617,
       0,     0,   662,     0,   619,   663,  1176,     0,     0,   619,
       0,  1178,     0,     0,  1177,   665,     0,   663,   663,  1179,
       0,   662,  1180,   663,  1182,     0,   662,   665,   665,     0,
    1181,     0,  1183,   665,     0,  1186,  1190,   662,  1192,   662,
    1194,  1196,   663,  1187,  1191,     0,  1193,   663,  1195,  1197,
     662,   662,   665,   662,  1198,   662,   662,   665,   663,     0,
     663,     0,  1199,     0,     0,  1200,     0,     0,   665,   662,
     665,   663,   663,  1201,   663,     0,   663,   663,     0,     0,
     662,   665,   665,  1202,   665,     0,   665,   665,  1204,  1206,
     663,  1203,     0,     0,     0,     0,  1205,  1207,   662,     0,
     665,   663,     0,   662,   662,     0,     0,     0,     0,     0,
       0,   665,     0,     0,     0,     0,     0,     0,     0,   663,
       0,     0,     0,     0,   663,   663,     0,     0,     0,   665,
       0,     0,     0,     0,   665,   665
  };

  /* YYCHECK.  */
  const short int
  mcmas_parser::yycheck_[] =
  {
        28,   435,    71,   329,    73,   439,   312,   494,   460,   496,
     100,   326,   246,   338,   320,   202,   925,   342,    83,   243,
     207,    66,    71,   204,    73,   116,   268,   116,   270,   345,
      40,   455,     1,   212,    71,   915,   338,   339,   338,   339,
     140,    78,   506,    71,   468,    73,   698,   212,   148,    77,
      78,   230,     1,   204,   934,   206,     1,   552,    27,   711,
     302,   435,   436,   213,   214,   230,    26,   232,     1,    18,
     244,    15,    17,   111,     7,   103,   435,   436,     1,   253,
     149,   686,   687,   688,    17,   530,   531,   532,     1,    15,
     190,   692,   693,   694,   163,   164,   536,   537,   538,    58,
     149,   129,   130,     1,    73,    62,    63,    66,   118,    42,
       7,     8,   149,    11,   163,   164,    15,    40,  1027,  1025,
    1026,   149,   172,   173,   174,    17,     1,    72,    72,   445,
      43,   200,     7,     8,     1,   163,   164,     1,   187,    72,
     168,   169,   170,     7,   172,   173,   174,   175,   176,   177,
     178,   200,    17,   244,  1034,   115,   335,   185,   186,   187,
     188,   189,   253,   200,   253,   316,   266,   267,     1,   269,
     335,   336,   200,    72,    72,    72,   204,     1,   243,     1,
      72,   219,   220,     7,   222,   213,   214,   178,   338,   339,
     233,   341,   507,     0,   185,   186,   241,    72,     1,   515,
    1106,  1107,    17,   519,  1110,    72,     9,    72,    72,   359,
     360,    44,   436,   282,   438,     3,   381,     1,    15,   288,
     289,   455,    42,   525,   526,   525,   526,   277,     1,    17,
      44,   533,   666,   282,   468,   459,   305,     1,   480,   481,
       1,   483,     3,   271,   313,   282,   698,   275,    72,   277,
      72,   279,    72,   281,   282,    43,   305,    72,    72,   711,
     288,   289,    46,    66,   313,    68,   700,     1,   305,   733,
     734,    44,   736,     7,     8,    72,   313,   305,   459,    28,
      17,   933,   241,   888,    72,   313,   710,   782,   279,   890,
      23,   319,   666,   467,   789,   790,   791,   792,   793,   794,
     795,   796,   747,    64,   678,   679,     1,   666,    72,   749,
     338,   339,     7,   341,   342,   689,     1,  1223,  1224,   678,
     679,     1,    71,    63,    73,     1,   700,     7,    77,    78,
      70,   359,   360,   371,   372,    72,    21,    22,    72,     1,
      73,   700,    27,     1,     7,     1,   511,     1,     1,     1,
       9,     7,     8,   669,   103,    95,     1,   673,     1,    25,
       5,    27,     1,    29,   407,   408,    42,   457,   411,   412,
     413,   414,   415,   416,   417,    34,   467,    72,   443,   479,
      32,     1,    45,   426,    46,    72,    44,    72,    73,    42,
      15,     1,    72,   543,   544,    61,    62,    17,   138,   139,
     149,     1,    45,    69,     1,     1,    31,   147,     8,    72,
       7,    21,    22,     1,   163,   164,    72,    27,    72,   168,
     169,   170,   738,   172,   173,   174,   175,   176,   177,   178,
       1,   756,     1,    72,   419,    72,   185,   186,   187,   188,
     189,    10,   427,    31,    40,   473,   474,    72,     1,   477,
     478,   200,    72,   502,   756,   204,   756,   506,   682,   683,
     684,   895,    72,    73,   213,   214,     1,   767,   768,    40,
      15,   137,    72,     1,   502,    72,   710,   701,   506,   721,
       8,   933,   916,   917,    72,    20,    31,   231,    41,    17,
     954,   955,    27,    21,    22,     1,     1,   525,   526,    27,
       5,     7,   530,   531,   532,   533,   534,   535,   536,   537,
     538,   539,   540,   541,   542,   543,   544,   704,   546,     1,
     701,   895,   271,   551,   552,   265,   275,    72,   277,     1,
     279,    42,   281,   282,  1021,     7,   895,    72,    73,   288,
     289,     1,   916,   917,    72,    73,     1,    15,   907,   908,
     701,    11,   703,     1,    42,    10,   305,   916,   917,    41,
       1,    72,     1,    31,   313,    20,    72,     8,     9,    17,
     319,     1,    27,    21,    22,    16,    17,   620,   621,    27,
      21,    22,     1,   626,    72,     1,    27,    17,     7,   338,
     339,     7,   341,   342,   637,   638,    37,    38,    39,     1,
      72,    42,   928,    42,    72,     1,     8,    42,     4,   652,
     359,   360,    72,   656,   657,   658,   659,   923,    73,   662,
     663,     1,   665,     3,    72,    73,    67,   943,     1,   945,
       1,    72,    73,    32,    33,     8,    32,    17,     9,   383,
       1,   385,    72,   387,   388,   389,   390,   391,   392,   393,
    1024,  1025,  1026,    72,     1,    16,    72,     1,   882,   403,
       7,     8,   886,    43,   733,   734,     1,    69,    70,    71,
     894,     1,  1106,     8,    21,    22,    37,     7,     7,     6,
      27,    42,    12,     1,   733,   734,    47,   736,    35,    18,
      34,    38,    72,     1,     1,    66,   733,    68,   922,    72,
      28,     9,    46,     1,    34,   733,   734,     1,   736,    16,
       1,     1,    39,    42,    10,     9,    46,   745,     1,   747,
      67,   749,    42,   751,    42,    72,    73,   755,   756,     1,
      37,     3,  1106,  1107,     1,    42,  1110,    72,     1,   767,
     768,    39,    72,    72,    34,    73,     1,  1106,  1107,    77,
     778,    42,   780,   502,   782,    45,    46,   506,    66,    42,
      68,   789,   790,   791,   792,   793,   794,   795,   796,   920,
      73,    43,    66,    40,    68,   103,   525,   526,    41,    34,
       1,   530,   531,   532,   533,   534,   535,   536,   537,   538,
     539,   540,   541,   542,   543,   544,  1112,   546,     1,     1,
       6,     1,   551,   552,     1,     5,     9,     1,     1,    12,
      13,     1,    15,    15,     7,     8,     1,     1,     8,    40,
      41,    24,    25,    26,    17,     1,    72,    17,    21,    22,
      39,    21,    22,    39,    27,   579,   580,    27,    31,    41,
     168,   169,   170,   587,    41,    38,    40,  1221,  1222,  1223,
    1224,     1,  1226,   597,   598,    40,    41,    41,     8,     9,
    1234,     1,  1236,    66,    40,    68,    16,    17,   612,     1,
       1,  1245,   616,   617,    67,   619,   204,    67,     1,    72,
      73,     1,    72,    73,     1,    17,     9,    37,    38,    21,
      22,    41,    42,    16,  1210,    27,  1212,     1,    32,     1,
      40,    41,    19,   952,   953,   954,   955,    11,     1,    40,
      41,     1,     1,     1,    37,     8,     9,     7,     8,    42,
      40,    23,    72,    16,   952,   953,   954,   955,    21,    22,
       1,    21,    22,    43,    27,    23,    40,    27,     9,     1,
      72,    73,     1,   271,    37,    38,    39,   275,    38,    42,
       1,    40,    11,   281,   997,   998,   999,  1000,  1001,  1002,
    1003,  1004,  1005,  1006,  1007,  1008,  1009,  1010,  1011,  1012,
    1013,  1014,  1015,  1016,    67,     1,     7,    67,    40,    72,
      73,    40,    72,    73,   733,   734,     1,   736,  1037,    40,
    1039,   319,    10,     1,     1,    66,   745,    68,   747,     1,
     749,     8,   751,    11,     1,    31,   755,   756,    39,  1037,
      17,  1039,     1,     1,    21,    22,     1,     6,   767,   768,
      27,     9,    19,     1,     9,    40,    14,     1,    16,   778,
       1,   780,    40,   782,    18,    10,     7,     8,    40,    36,
     789,   790,   791,   792,   793,   794,   795,   796,     1,     1,
      21,    22,     5,     6,     7,     8,    27,    31,    42,    12,
      13,    39,    15,    16,    17,    72,    73,    38,    21,    22,
      42,    24,    25,    26,    27,    28,    29,    30,    66,     1,
      68,    66,    35,    68,    37,    38,    39,    39,    41,     4,
       1,     1,    14,     1,    16,     1,    67,     6,     1,     8,
       1,    72,    73,     9,    19,    14,     7,    16,    11,    15,
      16,    19,    65,    66,    67,    68,     5,    32,     1,    72,
      73,     4,    32,    33,     7,     8,     1,    42,    39,    12,
      13,    37,    15,    16,    17,     1,    42,    40,    21,    22,
      15,    24,    25,    26,    27,    28,    29,    30,    14,    32,
       1,    15,     1,     4,    37,    38,     7,     8,    41,    42,
       9,    12,    13,    72,    15,    16,    25,    16,    27,     1,
      21,    22,    12,    24,    25,    26,    27,    28,    29,    30,
      11,    32,    65,    66,    67,    68,    37,    38,    37,    72,
      73,    42,     1,    42,     1,     1,     1,    41,     7,     8,
       6,     8,    61,   952,   953,   954,   955,    39,    17,    40,
      17,    42,    21,    22,    65,    66,    67,    68,    27,     1,
       1,    72,    73,   188,   189,    11,    35,    32,    33,    38,
       1,    38,    13,   977,   978,   979,   980,   981,   982,   983,
     984,   985,   986,   987,   988,   989,   990,   991,   992,   993,
     994,   995,   996,    72,    40,     1,    42,    39,    67,     5,
       6,     7,     8,    72,    73,    72,    12,    13,    39,    15,
      16,     1,     4,    72,     1,    21,    22,     4,    24,    25,
      26,    27,    28,    29,    30,    15,     1,    19,  1037,    35,
    1039,    37,    38,    39,     3,     1,    11,     1,     4,     6,
      32,     8,     1,     7,     8,     4,     5,    14,     7,    16,
       1,    10,    11,    17,    72,     6,    15,    21,    22,    65,
      66,    67,    68,    27,     1,    40,    72,    73,     5,     6,
       7,     8,     1,    32,    38,    12,    13,     1,    15,    16,
      39,     1,     1,     7,    21,    22,    15,    24,    25,    26,
      27,    28,    29,    30,    72,    15,     1,    16,    35,     1,
      37,    38,    39,    67,     9,    72,     8,     1,    72,    73,
       1,    16,     3,    72,     6,    17,     8,     1,    37,    21,
      22,    15,    14,    42,    16,    27,     1,    11,    65,    66,
      67,    68,    37,     8,     9,    72,    73,    12,    13,     1,
      15,    16,    17,     1,     4,     1,    21,    22,    10,    24,
      25,    26,    27,    28,    29,    30,    40,    15,    72,    15,
       1,     1,    37,    38,    39,    67,    41,    42,     8,     1,
      72,    73,    32,     1,    15,     1,     8,     9,    41,    39,
      72,    21,    22,    72,    16,    17,    14,    27,     1,    15,
      65,    66,    67,    68,    72,     8,     9,    72,    73,    12,
      13,    14,    15,    16,    17,    37,    38,     1,    21,    22,
      42,    24,    25,    26,    27,    28,    29,    30,     1,    72,
       1,    15,     1,     1,    37,     8,    39,    67,    41,    42,
       8,     1,    72,    73,    15,     1,     1,    16,     1,    17,
      72,     1,     8,    21,    22,    72,    16,    10,     8,    27,
       1,    16,    65,    66,    67,    68,     7,     8,    37,    72,
      73,    12,    13,    42,    15,    16,    17,    37,    47,    39,
      21,    22,    37,    24,    25,    26,    27,    28,    29,    30,
     397,   398,    47,   400,    35,    72,    37,    38,    39,     1,
      41,    56,     4,     1,    72,    73,     4,     5,     1,     7,
       1,     1,    10,    11,     1,     1,     9,    15,     4,    10,
      10,    14,     9,    16,    65,    66,    67,    68,     1,    16,
      32,    72,    73,    19,    32,     8,     9,    10,    72,    12,
      13,    39,    15,    16,    17,     1,    32,     1,    21,    22,
      37,    24,    25,    26,    27,    28,    29,    30,     1,    15,
      47,    15,     1,     1,    37,    38,    39,    10,    41,     8,
       1,     1,     1,    66,    72,    68,     7,    15,    17,     9,
       9,     1,    21,    22,     1,    44,    16,    16,    27,     1,
       1,     8,    65,    66,    67,    68,     8,     8,     9,    72,
      73,    12,    13,    72,    15,    16,    17,    37,    37,    39,
      21,    22,    42,    24,    25,    26,    27,    28,    29,    30,
      31,   421,   422,    72,   424,     1,    37,    38,    34,     1,
      41,    42,     8,    72,    73,     1,    66,     9,    68,    45,
      46,    10,     1,     9,    16,    21,    22,     4,     5,     8,
      16,    27,     1,    10,    65,    66,    67,    68,    15,     8,
       9,    72,    73,    12,    13,    37,    15,    16,    17,    72,
      42,    37,    21,    22,    45,    24,    25,    26,    27,    28,
      29,    30,    39,     9,     9,    32,    33,     1,    37,    38,
      16,    16,    41,    42,     8,     1,    72,    73,     1,     1,
      32,    33,     8,     9,     7,     7,   396,    21,    22,   399,
      16,    17,   420,    27,     1,   423,    65,    66,    67,    68,
      72,     8,     9,    72,    73,    12,    13,    14,    15,    16,
      17,    37,    38,     1,    21,    22,    42,    24,    25,    26,
      27,    28,    29,    30,    72,   695,   696,   697,    16,     1,
      37,     3,    39,     1,    41,    42,     1,     1,    72,    73,
      14,     9,    16,    72,     9,     9,    72,    72,    16,    37,
       5,    16,    16,    72,    42,    10,     1,    72,    65,    66,
      15,    68,    72,     8,     9,    72,    73,    12,    13,    37,
      15,    16,    37,    37,    42,    39,    21,    22,    42,    24,
      25,    26,    27,    28,    29,    30,    32,    33,     1,     1,
     690,   691,    37,    38,    39,     8,     9,    42,    73,    12,
      13,    14,    15,    16,    16,   175,   176,   177,    21,    22,
       1,    24,    25,    26,    27,    28,    29,    30,     9,    72,
      65,    66,    67,    68,    37,    37,    39,    72,    73,    42,
       1,    15,     1,     1,     3,    47,    27,    28,     9,   534,
     535,     9,     1,     3,    56,    16,    72,     1,    16,     3,
       9,    72,    65,    66,    67,    68,     1,    16,    72,    72,
      73,    41,    41,     8,     9,    10,    37,    12,    13,    37,
      15,    16,    72,   972,    42,   974,    21,    22,    37,    24,
      25,    26,    27,    28,    29,    30,    41,    72,    47,     1,
      41,    72,    37,    38,    39,    72,     8,     9,    72,    72,
      12,    13,    72,    15,    16,    17,   539,   540,   541,    21,
      22,     1,    24,    25,    26,    27,    28,    29,    30,    72,
      65,    66,    67,    68,    72,    37,    16,    72,    73,    41,
      42,     1,    72,     5,     1,    72,    72,    72,    10,    72,
       1,    72,     9,    15,    72,    72,    16,    37,    72,    16,
      72,     1,    42,    65,    66,    67,    68,    47,     8,     9,
      72,    73,    12,    13,    72,    15,    16,    37,    72,    39,
      37,    21,    22,    72,    24,    25,    26,    27,    28,    29,
      30,    31,     5,     1,    72,    72,    25,    37,    38,    58,
       8,     9,    42,   260,    12,    13,    14,    15,    16,    17,
     118,   253,   329,    21,    22,     1,    24,    25,    26,    27,
      28,    29,    30,     8,   251,    65,    66,    67,    68,    37,
      16,    39,    72,    73,    42,   245,     4,     5,   204,   928,
     701,    34,    10,    11,   105,   379,     1,    15,   576,   976,
     212,    37,   810,   403,     9,     1,    42,    65,    66,    -1,
      68,    47,     8,     9,    72,    73,    12,    13,    14,    15,
      16,    39,    27,    28,   395,    21,    22,    -1,    24,    25,
      26,    27,    28,    29,    30,    -1,    -1,     1,     1,    -1,
      -1,    37,    -1,    39,     8,     9,    42,    -1,    12,    13,
      14,    15,    16,    16,    -1,    -1,     1,    21,    22,    -1,
      24,    25,    26,    27,    28,    29,    30,     1,    -1,    65,
      66,    16,    68,    37,    37,    39,    72,    73,    42,     0,
       1,    -1,    16,     1,    47,    -1,    -1,     8,    -1,    -1,
      -1,    12,    37,    56,    -1,    16,    17,    42,    16,    -1,
      -1,    65,    66,    37,    68,    -1,    -1,    -1,    72,    73,
      -1,    -1,    -1,    47,    -1,    -1,    37,    38,    -1,    37,
      -1,    42,    56,    -1,    42,    46,    47,    48,    49,    50,
      51,    52,    53,    54,    55,     1,    57,    58,    59,    60,
      61,     1,    -1,     9,    -1,    -1,    -1,    -1,     8,     9,
      16,    72,    12,    13,    -1,    15,    16,    17,    -1,    -1,
      -1,    21,    22,     1,    24,    25,    26,    27,    28,    29,
      30,    37,    -1,     1,    -1,    -1,    42,    37,    16,    -1,
       1,    41,    42,    -1,    12,    13,    -1,    15,     9,    -1,
      -1,    -1,    -1,    -1,    -1,    16,    24,    25,    26,    37,
      66,    -1,    68,     1,    42,    65,    66,    -1,    68,    -1,
       8,     9,    72,    73,    12,    13,    37,    15,    16,    17,
      -1,    42,    -1,    21,    22,    -1,    24,    25,    26,    27,
      28,    29,    30,    -1,    -1,     1,    -1,     1,    66,    37,
      68,    -1,     8,     9,    42,     9,    12,    13,    14,    15,
      16,    17,    -1,    -1,    -1,    21,    22,    -1,    24,    25,
      26,    27,    -1,    27,    28,    -1,    -1,    65,    66,    -1,
      68,    37,     1,    39,    72,    73,    42,    -1,    -1,     8,
       9,    -1,    -1,    12,    13,    14,    15,    16,    -1,    -1,
      -1,    -1,    21,    22,    -1,    24,    25,    26,    27,    65,
      66,    67,    68,    -1,     1,    -1,    72,    73,    37,    -1,
      39,     8,     9,    42,    -1,    12,    13,    -1,    15,    16,
      17,    -1,    -1,     1,    21,    22,     1,    24,    25,    26,
      27,     9,    -1,     8,     9,    -1,    65,    66,    67,    68,
      37,    16,    17,    72,    73,    42,    21,    22,    -1,    27,
      28,    -1,    27,    -1,    -1,    -1,    -1,    -1,     1,    -1,
      -1,    -1,    37,    38,    39,     8,     9,    42,    65,    66,
      67,    68,     1,    16,    17,    72,    73,    -1,    21,    22,
       9,    -1,    -1,     1,    27,     1,    -1,    16,    31,    -1,
      -1,     9,    67,     9,    37,    38,     1,    72,    73,    42,
      16,    -1,    -1,     8,     9,    -1,    -1,    -1,    37,    27,
      28,    16,    17,    -1,    -1,    -1,    21,    22,    47,    -1,
       1,    37,    27,    -1,    67,    -1,    31,     8,     9,    72,
      73,    47,    37,    38,    -1,    16,    -1,    42,     1,    -1,
      21,    22,    -1,    -1,     1,    -1,    27,    -1,    -1,    -1,
      -1,     8,     9,    16,    -1,    -1,    37,    38,    39,    16,
      17,    42,    67,     1,    21,    22,    -1,    72,    73,     1,
      27,     9,    -1,     1,    37,    -1,    -1,     9,    16,    42,
      37,    38,     1,    -1,    -1,    42,    67,    -1,    16,     8,
       9,    72,    73,    -1,    -1,    27,    28,    16,    17,    37,
      -1,    39,    21,    22,    42,     1,    -1,    -1,    27,    37,
      67,    -1,     8,     9,    42,    72,    73,    -1,    37,    38,
      16,     1,    -1,    42,     4,    21,    22,    -1,    66,     1,
      68,    27,    -1,    -1,    -1,    31,     8,     9,    18,    19,
      -1,    37,    38,    -1,    16,    -1,    42,    -1,    67,    21,
      22,    -1,    32,    72,    73,    27,    -1,    -1,    -1,    31,
      -1,    -1,     1,    -1,    -1,    37,    38,    -1,     7,     8,
      42,    67,     1,    -1,    -1,    -1,    72,    73,    17,    -1,
       9,     1,    21,    22,     1,    -1,     1,    16,    27,     9,
       7,     8,    31,     8,    -1,    67,    16,    -1,    -1,    38,
      72,    73,    17,    -1,    21,    22,    21,    22,    37,     1,
      27,    -1,    27,    42,    -1,     7,     8,    37,    35,    -1,
      35,    38,    42,    38,    -1,    17,    -1,    47,    67,    21,
      22,    -1,    -1,    72,    73,    27,    56,     1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,     9,    38,     1,    12,    13,
      67,    15,    67,     7,     8,    72,    73,    72,    73,    -1,
      24,    25,    26,    17,    -1,    -1,    -1,    21,    22,    -1,
       1,    -1,     1,    27,    -1,    67,     7,     8,     7,     8,
      72,    73,    -1,    -1,    38,    -1,    17,    -1,    17,    -1,
      21,    22,    21,    22,     1,    -1,    27,    -1,    27,    -1,
       7,     8,    66,    -1,    68,    -1,    -1,    38,    -1,    38,
      17,     1,    -1,    67,    21,    22,    -1,    -1,    72,    73,
      27,    -1,    -1,    -1,    -1,    -1,    16,    -1,    -1,    -1,
       1,    38,    -1,     1,    -1,    -1,    67,     8,    67,    10,
       8,    72,    73,    72,    73,    -1,    17,    37,     1,    17,
      21,    22,    42,    21,    22,     8,    27,    -1,    -1,    27,
      67,    -1,     1,    31,    17,    72,    73,    38,    21,    22,
      38,     1,    -1,    -1,    27,    -1,    -1,    16,     8,    -1,
      10,    -1,    -1,    -1,    -1,    38,     1,    -1,    -1,    -1,
      -1,    21,    22,     8,    -1,    -1,    67,    27,    37,    67,
      -1,    72,    73,    42,    72,    73,    21,    22,    38,     1,
      -1,    -1,    27,     1,    67,    -1,     8,    -1,    -1,    72,
      73,     9,    -1,    38,     1,    17,    -1,    -1,    16,    21,
      22,     8,    -1,     1,    -1,    27,    -1,    67,    -1,    -1,
      -1,     9,    72,    73,    21,    22,    38,    -1,    16,    37,
      27,    -1,    67,     1,    31,    -1,     1,    72,    73,    47,
      -1,    38,     7,     8,    12,    13,    -1,    15,    56,    37,
      -1,    16,    17,    -1,    42,    67,    24,    25,    26,    -1,
      72,    73,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    34,
      67,    -1,    37,    38,    -1,    72,    73,    42,    66,    -1,
      68,    46,    47,    48,    49,    50,    51,    52,    53,    54,
      55,    -1,    57,    58,    59,    60,    61,     1,    66,    -1,
      68,    -1,    -1,    -1,     8,     9,    -1,    72,    12,    -1,
      -1,    -1,    16,    17,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,     1,    -1,     1,    -1,    -1,    -1,    -1,    -1,
       9,     8,     9,    37,    38,    12,    -1,    16,    42,    16,
      17,    -1,    -1,    47,    48,    49,    50,    51,    52,    53,
      54,    55,    56,    57,    58,    59,    60,    61,    37,    -1,
      37,    38,    -1,    42,    -1,    42,    -1,    -1,    72,    -1,
      47,    48,    49,    50,    51,    52,    53,    54,    55,    56,
      57,    58,    59,    60,    61,     1,    -1,    66,    -1,    68,
      -1,    -1,     8,     9,    -1,    72,    12,    -1,    -1,    -1,
      16,    17,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
       1,    -1,     1,    -1,    -1,    -1,    -1,    -1,     9,     8,
       9,    37,    38,    12,    -1,    16,    42,    16,    17,    -1,
      -1,    47,    48,    49,    50,    51,    52,    53,    54,    55,
      56,    57,    58,    59,    60,    61,    37,    -1,    37,    38,
      -1,    42,    -1,    42,    -1,    -1,    72,    -1,    47,    48,
      49,    50,    51,    52,    53,    54,    55,    56,    57,    58,
      59,    60,    61,     1,    -1,    -1,    -1,     1,    -1,    -1,
       8,     9,    -1,    72,    12,     9,    -1,    -1,    16,    17,
      -1,    -1,    16,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
       1,    -1,    -1,    -1,    -1,    -1,    -1,     8,     9,    37,
      38,    12,    -1,    37,    42,    16,    17,    -1,    42,    47,
      48,    49,    50,    51,    52,    53,    54,    55,    56,    57,
      58,    59,    60,    61,    -1,    -1,    37,    38,    -1,    -1,
      -1,    42,    -1,    -1,    72,    -1,    47,    48,    49,    50,
      51,    52,    53,    54,    55,    56,    57,    58,    59,    60,
      61,     1,    -1,    -1,    -1,     1,    -1,    -1,     8,     9,
      -1,    72,    12,     9,    -1,    -1,    16,    17,    -1,    -1,
      16,    -1,    -1,    -1,    -1,    -1,    -1,    -1,     1,    -1,
      -1,    -1,    -1,    -1,    -1,     8,     9,    37,    38,    12,
      -1,    37,    42,    16,    17,    -1,    42,    47,    48,    49,
      50,    51,    52,    53,    54,    55,    56,    57,    58,    59,
      60,    61,    -1,    -1,    37,    38,    -1,    -1,    -1,    42,
      -1,    -1,    72,    -1,    47,    48,    49,    50,    51,    52,
      53,    54,    55,    56,    57,    58,    59,    60,    61,     1,
      -1,    -1,    -1,     1,    -1,    -1,     8,     9,    -1,    72,
      12,     9,    -1,    -1,    16,    17,    -1,    -1,    16,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,     1,    -1,    -1,    -1,
      -1,    -1,    -1,     8,     9,    37,    38,    12,    -1,    37,
      42,    16,    17,    -1,    42,    47,    48,    49,    50,    51,
      52,    53,    54,    55,    56,    57,    58,    59,    60,    61,
      -1,    -1,    37,    38,    -1,    -1,    -1,    42,    -1,    -1,
      72,    -1,    47,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,    61,     1,    -1,    -1,
      -1,     1,    -1,    -1,     8,     9,    -1,    72,    12,     9,
      -1,    -1,    16,    17,    -1,    -1,    16,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,     1,    -1,    -1,    -1,    -1,    -1,
      -1,     8,     9,    37,    38,    12,    -1,    37,    42,    16,
      17,    -1,    42,    47,    48,    49,    50,    51,    52,    53,
      54,    55,    56,    57,    58,    59,    60,    61,    -1,    -1,
      37,    38,    -1,    -1,    -1,    42,    -1,    -1,    72,    -1,
      47,    48,    49,    50,    51,    52,    53,    54,    55,    56,
      57,    58,    59,    60,    61,     1,    -1,    -1,    -1,     1,
      -1,    -1,     8,     9,    -1,    72,    12,     9,    -1,    -1,
      16,    17,    -1,    -1,    16,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,     1,    -1,    -1,    -1,    -1,    -1,    -1,     8,
       9,    37,    38,    12,    -1,    37,    42,    16,    17,    -1,
      42,    47,    48,    49,    50,    51,    52,    53,    54,    55,
      56,    57,    58,    59,    60,    61,    -1,    -1,    37,    38,
      -1,    -1,    -1,    42,    -1,    -1,    72,    -1,    47,    48,
      49,    50,    51,    52,    53,    54,    55,    56,    57,    58,
      59,    60,    61,     1,    -1,    -1,    -1,     1,    -1,    -1,
       8,     9,    -1,    72,    12,     9,    -1,    -1,    16,    17,
      -1,    -1,    16,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
       1,    -1,    -1,    -1,    -1,    -1,    -1,     8,     9,    37,
      38,    12,    -1,    37,    42,    16,    17,    -1,    42,    47,
      48,    49,    50,    51,    52,    53,    54,    55,    56,    57,
      58,    59,    60,    61,    -1,    -1,    37,    38,    -1,    -1,
      -1,    42,    -1,    -1,    72,    -1,    47,    48,    49,    50,
      51,    52,    53,    54,    55,    56,    57,    58,    59,    60,
      61,     1,    -1,    -1,    -1,     1,    -1,    -1,     8,     9,
      -1,    72,    12,     9,    -1,    -1,    16,    17,    -1,    -1,
      16,    -1,    -1,    -1,    -1,    -1,    -1,    -1,     1,    -1,
      -1,    -1,    -1,    -1,    -1,     8,     9,    37,    38,    12,
      -1,    37,    42,    16,    17,    -1,    42,    47,    48,    49,
      50,    51,    52,    53,    54,    55,    56,    57,    58,    59,
      60,    61,    -1,    -1,    37,    38,    -1,    -1,    -1,    42,
      -1,    -1,    72,    -1,    47,    48,    49,    50,    51,    52,
      53,    54,    55,    56,    57,    58,    59,    60,    61,     1,
      -1,    -1,    -1,     1,    -1,    -1,     8,     9,    -1,    72,
      12,     9,    -1,    -1,    16,    17,    -1,    -1,    16,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,     1,    -1,    -1,    -1,
      -1,    -1,    -1,     8,     9,    37,    38,    12,    -1,    37,
      42,    16,    17,    -1,    42,    47,    48,    49,    50,    51,
      52,    53,    54,    55,    56,    57,    58,    59,    60,    61,
      -1,    -1,    37,    38,    -1,    -1,    -1,    42,    -1,    -1,
      72,    -1,    47,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,    61,     1,    -1,    -1,
      -1,    -1,    -1,     7,     8,    -1,     1,    72,    12,    -1,
      -1,    -1,    16,    17,     9,    -1,    -1,    -1,    -1,    -1,
      -1,    16,     1,    -1,     1,    -1,    -1,    -1,    -1,    -1,
       9,     8,     9,    37,    38,    -1,    -1,    16,    42,    16,
      17,    -1,    37,    47,    48,    49,    50,    51,    52,    53,
      54,    55,    47,    57,    58,    59,    60,    61,    37,    -1,
      37,    38,    -1,    42,    -1,    42,    -1,    -1,    72,    -1,
      47,    48,    49,    50,    51,    52,    53,    54,    55,    56,
      57,    58,    59,    60,    61,     1,    -1,    -1,    -1,     1,
      -1,    -1,     8,     9,    -1,    72,    -1,     9,    -1,    -1,
      16,    17,    -1,    -1,    16,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,     1,    -1,    -1,    -1,    -1,    -1,    -1,
       8,    37,    38,    -1,    -1,    37,    42,    39,    16,    17,
      42,    47,    48,    49,    50,    51,    52,    53,    54,    55,
      56,    57,    58,    59,    60,    61,    34,    -1,    -1,    37,
      38,    -1,    -1,    -1,    42,    -1,    72,    -1,    46,    47,
      48,    49,    50,    51,    52,    53,    54,    55,     1,    57,
      58,    59,    60,    61,     1,    -1,     9,     1,    -1,    -1,
      -1,     8,     9,    16,    72,     9,    -1,    -1,    -1,    16,
      17,    -1,    16,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,     1,    -1,    -1,    37,    -1,    -1,    -1,     8,     9,
      37,    38,    -1,    37,    47,    42,    16,    17,    42,    -1,
      47,    48,    49,    50,    51,    52,    53,    54,    55,    56,
      57,    58,    59,    60,    61,    -1,    -1,    37,    38,    -1,
      -1,    -1,    42,    -1,    -1,    72,    -1,    47,    48,    49,
      50,    51,    52,    53,    54,    55,    56,    57,    58,    59,
      60,    61,     1,    -1,    -1,     1,     1,    -1,    -1,     8,
       9,    -1,    72,     9,     9,    -1,    -1,    16,    17,    -1,
      16,    16,    -1,    -1,    -1,    -1,    -1,    -1,    -1,     1,
      -1,    -1,    -1,    -1,    -1,    -1,     8,     9,    37,    38,
      -1,    37,    37,    42,    16,    17,    42,    42,    47,    48,
      49,    50,    51,    52,    53,    54,    55,    56,    57,    58,
      59,    60,    61,    -1,    -1,    37,    38,    -1,    -1,    -1,
      42,    -1,    -1,    72,    -1,    47,    48,    49,    50,    51,
      52,    53,    54,    55,    56,    57,    58,    59,    60,    61,
       1,    -1,    -1,     1,    -1,    -1,    -1,     8,     9,    -1,
      72,     9,    -1,    -1,    -1,    16,    17,    -1,    16,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,     1,    -1,    -1,
      -1,    -1,    -1,    -1,     8,     9,    37,    38,    -1,    37,
      -1,    42,    16,    17,    42,    -1,    47,    48,    49,    50,
      51,    52,    53,    54,    55,    56,    57,    58,    59,    60,
      61,    -1,    -1,    37,    38,    -1,    -1,    -1,    42,    -1,
      -1,    72,    -1,    47,    48,    49,    50,    51,    52,    53,
      54,    55,    56,    57,    58,    59,    60,    61,     1,    -1,
      -1,    -1,    -1,    -1,    -1,     8,     9,    -1,    72,    -1,
      -1,    -1,    -1,    16,    17,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,     1,    -1,    -1,    -1,    -1,
      -1,    -1,     8,     9,    37,    38,    -1,    -1,    -1,    42,
      16,    17,    -1,    -1,    47,    48,    49,    50,    51,    52,
      53,    54,    55,    56,    57,    58,    59,    60,    61,    -1,
      -1,    37,    38,    -1,    -1,    -1,    42,    -1,    -1,    72,
      -1,    47,    48,    49,    50,    51,    52,    53,    54,    55,
      56,    57,    58,    59,    60,    61,     1,    -1,    -1,    -1,
      -1,    -1,    -1,     8,     9,    -1,    72,    -1,    -1,    -1,
      -1,    16,    17,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,     1,    -1,    -1,    -1,    -1,    -1,    -1,
       8,     9,    37,    38,    -1,    -1,    -1,    42,    16,    17,
      -1,    -1,    47,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,    61,    -1,    -1,    37,
      38,    -1,    -1,    -1,    42,    -1,    -1,    72,    -1,    47,
      48,    49,    50,    51,    52,    53,    54,    55,    56,    57,
      58,    59,    60,    61,     1,    -1,    -1,    -1,    -1,    -1,
      -1,     8,     9,    -1,    72,    -1,    -1,    -1,    -1,    16,
      17,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,     1,    -1,    -1,    -1,    -1,    -1,    -1,     8,     9,
      37,    38,    -1,    -1,    -1,    42,    16,    17,    -1,    -1,
      47,    48,    49,    50,    51,    52,    53,    54,    55,    56,
      57,    58,    59,    60,    61,    -1,    -1,    37,    38,    -1,
      -1,    -1,    42,    -1,    -1,    72,    -1,    47,    48,    49,
      50,    51,    52,    53,    54,    55,    56,    57,    58,    59,
      60,    61,     1,    -1,    -1,    -1,    -1,    -1,    -1,     8,
       9,    -1,    72,    -1,    -1,    -1,    -1,    16,    17,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,     1,
      -1,    -1,    -1,    -1,    -1,    -1,     8,     9,    37,    38,
      -1,    -1,    -1,    42,    16,    17,    -1,    -1,    47,    48,
      49,    50,    51,    52,    53,    54,    55,    56,    57,    58,
      59,    60,    61,    -1,    -1,    37,    38,    -1,    -1,    -1,
      42,    -1,    -1,    72,    -1,    47,    48,    49,    50,    51,
      52,    53,    54,    55,    56,    57,    58,    59,    60,    61,
       1,    -1,    -1,    -1,    -1,    -1,    -1,     8,     9,    -1,
      72,    -1,    -1,    -1,    -1,    16,    17,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,     1,    -1,    -1,
      -1,    -1,    -1,    -1,     8,     9,    37,    38,    -1,    -1,
      -1,    42,    16,    17,    -1,    -1,    47,    48,    49,    50,
      51,    52,    53,    54,    55,    56,    57,    58,    59,    60,
      61,    -1,    -1,    37,    38,    -1,    -1,    -1,    42,    -1,
      -1,    72,    -1,    47,    48,    49,    50,    51,    52,    53,
      54,    55,    56,    57,    58,    59,    60,    61,     1,    -1,
      -1,    -1,    -1,    -1,    -1,     8,     9,    -1,    72,    -1,
      -1,    -1,    -1,    16,    17,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,     1,    -1,    -1,    -1,    -1,
      -1,    -1,     8,     9,    37,    38,    -1,    -1,    -1,    42,
      16,    17,    -1,    -1,    47,    48,    49,    50,    51,    52,
      53,    54,    55,    56,    57,    58,    59,    60,    61,    -1,
      -1,    37,    38,    -1,    -1,    -1,    42,    -1,    -1,    72,
      -1,    47,    48,    49,    50,    51,    52,    53,    54,    55,
      56,    57,    58,    59,    60,    61,     1,     1,    -1,    -1,
      -1,    -1,    -1,     8,    -1,     9,    72,    12,    12,    13,
      -1,    15,    17,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      24,    25,    26,     1,    -1,    -1,    -1,    32,    33,     7,
       8,    -1,    -1,    38,    12,    -1,    -1,    -1,    -1,    17,
      -1,    -1,    -1,    48,    49,    50,    51,    52,    53,    54,
      55,    -1,    57,    58,    59,    60,    61,    -1,    -1,    -1,
      38,    -1,    66,    -1,    68,    -1,    -1,    72,    -1,    -1,
      48,    49,    50,    51,    52,    53,    54,    55,     1,    57,
      58,    59,    60,    61,     1,    -1,     9,     1,    -1,    -1,
       7,     8,    -1,    16,    72,    12,    -1,    -1,    12,    13,
      17,    15,    -1,    -1,    -1,    -1,    -1,    -1,    -1,     1,
      24,    25,    26,    -1,    37,     7,     8,    40,    41,    -1,
      12,    38,    -1,    -1,    47,    17,    -1,    -1,    -1,    -1,
      -1,    48,    49,    50,    51,    52,    53,    54,    55,    -1,
      57,    58,    59,    60,    61,    -1,    38,    -1,    -1,    -1,
      -1,    -1,    66,    -1,    68,    72,    48,    49,    50,    51,
      52,    53,    54,    55,    -1,    57,    58,    59,    60,    61,
       1,     1,    -1,     1,    -1,    -1,    -1,     8,    -1,     9,
      72,     9,    12,    13,    -1,    15,    17,    -1,    16,    -1,
      -1,    -1,    -1,    -1,    24,    25,    26,     1,    -1,    -1,
      -1,    32,    33,     7,     8,    -1,    -1,    38,    -1,    37,
      -1,    39,    -1,    17,    42,    -1,    -1,    48,    49,    50,
      51,    52,    53,    54,    55,     1,    57,    58,    59,    60,
      61,    -1,    -1,     9,    38,    -1,    66,    -1,    68,    -1,
      16,    72,    -1,    -1,    48,    49,    50,    51,    52,    53,
      54,    55,    -1,    57,    58,    59,    60,    61,     1,    -1,
      -1,    37,    -1,    -1,    -1,     8,    42,     1,    72,    12,
      -1,    47,    -1,    -1,    17,     9,    -1,    -1,    -1,    -1,
      56,    -1,    16,     1,    -1,     1,    -1,    -1,    -1,     7,
       8,    -1,    -1,     9,    -1,    38,    -1,    -1,    -1,    17,
      16,    -1,    -1,    37,    -1,    48,    49,    50,    51,    52,
      53,    54,    55,    47,    57,    58,    59,    60,    61,    -1,
      38,    37,    56,    39,    -1,    -1,    42,    -1,    -1,    72,
      48,    49,    50,    51,    52,    53,    54,    55,    -1,    57,
      58,    59,    60,    61,     1,    -1,    -1,    -1,    -1,    -1,
      -1,     8,     4,     1,    72,    12,    -1,    -1,    10,    11,
      17,     9,    -1,    15,    -1,    -1,    -1,    19,    16,     1,
      -1,     1,    -1,    -1,    -1,     7,     8,    -1,    -1,     9,
      32,    38,    -1,    -1,    -1,    17,    16,    39,    -1,    37,
      -1,    48,    49,    50,    51,    52,    53,    54,    55,    47,
      57,    58,    59,    60,    61,    -1,    38,    37,    56,    39,
      -1,    -1,    42,    -1,    -1,    72,    48,    49,    50,    51,
      52,    53,    54,    55,     1,    57,    58,    59,    60,    61,
       1,    -1,     9,    -1,    -1,    -1,    -1,     8,    -1,    16,
      72,    12,    -1,    -1,    -1,    -1,    17,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,     1,    -1,     1,     1,    -1,
      37,     7,     8,    40,    41,     9,     9,    38,    -1,    -1,
      47,    17,    16,    16,    -1,    -1,    -1,    48,    49,    50,
      51,    52,    53,    54,    55,    -1,    57,    58,    59,    60,
      61,    -1,    38,    37,    37,    39,    39,    -1,    42,    42,
      -1,    72,    48,    49,    50,    51,    52,    53,    54,    55,
      -1,    57,    58,    59,    60,    61,     1,    -1,    -1,     1,
       1,    -1,    -1,     8,    -1,    -1,    72,     9,     9,    -1,
      12,    13,    17,    15,    16,    16,    -1,    -1,    -1,    -1,
      -1,     1,    24,    25,    26,    27,    28,    -1,     8,    -1,
      -1,    -1,    -1,    38,    -1,    37,    37,    17,    39,    -1,
      42,    42,    -1,    48,    49,    50,    51,    52,    53,    54,
      55,    -1,    57,    58,    59,    60,    61,    -1,    38,    -1,
      -1,    -1,    -1,    65,    66,    -1,    68,    72,    48,    49,
      50,    51,    52,    53,    54,    55,    -1,    57,    58,    59,
      60,    61,     1,    -1,    -1,    -1,    -1,    -1,     7,     8,
      -1,    -1,    72,     1,    -1,     1,    -1,    -1,    17,    -1,
      -1,     9,    -1,     9,    -1,    -1,    -1,    -1,    16,     1,
      16,    -1,    -1,    -1,    -1,    34,    -1,     9,    -1,    38,
      12,    13,    14,    15,    16,    44,    45,    46,    -1,    37,
      -1,    37,    24,    25,    26,    27,    28,    29,    30,    47,
      -1,    47,    -1,     1,     1,    37,    -1,    39,    -1,    -1,
      42,     9,     9,    72,    12,    13,    14,    15,    16,    16,
      -1,    -1,    -1,    -1,    -1,    -1,    24,    25,    26,    27,
      28,    29,    30,    65,    66,     1,    68,    -1,    -1,    37,
      37,    39,    39,     9,    42,    42,    12,    13,    14,    15,
      16,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    24,    25,
      26,    27,    28,    29,    30,    -1,    -1,    65,    66,     1,
      68,    37,    -1,    39,    -1,    -1,    42,     9,    -1,    -1,
      12,    13,    14,    15,    16,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    24,    25,    26,    27,    28,    29,    30,    65,
      66,     1,    68,    -1,    -1,    37,    -1,    39,    -1,     9,
      42,    -1,    12,    13,    14,    15,    16,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    24,    25,    26,    27,    28,    29,
      30,    -1,    -1,    65,    66,     1,    68,    37,    -1,    39,
      -1,    -1,    42,     9,    -1,    -1,    12,    13,    14,    15,
      16,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    24,    25,
      26,    27,    28,    29,    30,    65,    66,     1,    68,    -1,
      -1,    37,    -1,    39,    -1,     9,    42,    -1,    12,    13,
      14,    15,    16,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      24,    25,    26,    27,    28,    29,    30,    -1,    -1,    65,
      66,     1,    68,    37,    -1,    39,    -1,    -1,    42,     9,
      -1,    -1,    12,    13,    14,    15,    16,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    24,    25,    26,    27,    28,    29,
      30,    65,    66,     1,    68,    -1,    -1,    37,    -1,    39,
      -1,     9,    42,    -1,    12,    13,    -1,    15,    16,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    24,    25,    26,    27,
      28,    29,    30,    -1,    -1,    65,    66,     1,    68,    37,
      -1,    -1,    -1,    41,    42,     9,    -1,    -1,    12,    13,
      -1,    15,    16,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      24,    25,    26,    27,    28,    29,    30,    65,    66,    -1,
      68,     1,    -1,    37,    -1,    -1,    -1,    41,    42,     9,
      -1,    -1,    12,    13,    -1,    15,    16,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    24,    25,    26,    27,    28,    29,
      30,    65,    66,    -1,    68,     1,     1,    37,    -1,    -1,
      -1,    41,    42,     9,     9,    -1,    12,    13,    14,    15,
      16,    16,    -1,    -1,    -1,    -1,    -1,    -1,    24,    25,
      26,    27,    28,    -1,    -1,    65,    66,     1,    68,    -1,
      -1,    37,    37,    39,    39,     9,    42,    42,    12,    13,
      14,    15,    16,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      24,    25,    26,    27,    28,    -1,    -1,    -1,    -1,    65,
      66,     1,    68,    37,    -1,    39,    -1,    -1,    42,     9,
      -1,    -1,    12,    13,    -1,    15,    16,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    24,    25,    26,    27,    28,    29,
      30,    65,    66,     1,    68,    -1,    -1,    37,    -1,    -1,
      -1,     9,    42,    -1,    12,    13,    14,    15,    16,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    24,    25,    26,    27,
      28,    -1,    -1,    -1,    -1,    65,    66,     1,    68,    37,
      -1,    39,    -1,    -1,    42,     9,    -1,    -1,    12,    13,
      14,    15,    16,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      24,    25,    26,    27,    28,    -1,    -1,    65,    66,     1,
      68,    -1,    -1,    37,    -1,    39,    -1,     9,    42,    -1,
      12,    13,    -1,    15,    16,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    24,    25,    26,    27,    28,    29,    30,    -1,
      -1,    65,    66,     1,    68,    37,    -1,    -1,    -1,    -1,
      42,     9,    -1,    -1,    12,    13,    -1,    15,    16,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    24,    25,    26,    27,
      28,    29,    30,    65,    66,     1,    68,    -1,    -1,    37,
      -1,    -1,    -1,     9,    42,    -1,    12,    13,    -1,    15,
      16,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    24,    25,
      26,    27,    28,    29,    30,    -1,    -1,    65,    66,     1,
      68,    37,    -1,    -1,    -1,    -1,    42,     9,    -1,    -1,
      12,    13,    14,    15,    16,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    24,    25,    26,    -1,    -1,    -1,    -1,    65,
      66,     1,    68,    -1,    -1,    37,    -1,    39,    -1,     9,
      42,    -1,    12,    13,    14,    15,    16,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    24,    25,    26,    -1,    -1,    -1,
      -1,    -1,    -1,    65,    66,     1,    68,    37,    -1,    39,
      -1,    -1,    42,     9,    -1,    -1,    12,    13,    14,    15,
      16,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    24,    25,
      26,    -1,    -1,    -1,    -1,    65,    66,     1,    68,    -1,
      -1,    37,    -1,    39,    -1,     9,    42,    -1,    12,    13,
      14,    15,    16,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      24,    25,    26,    -1,    -1,    -1,    -1,    -1,    -1,    65,
      66,     1,    68,    37,    -1,    39,    -1,    -1,    42,     9,
      -1,    -1,    12,    13,    14,    15,    16,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    24,    25,    26,    -1,    -1,    -1,
      -1,    65,    66,     1,    68,    -1,    -1,    37,     1,    39,
      -1,     9,    42,    -1,    12,    13,     9,    15,    16,    12,
      13,    -1,    15,    -1,    -1,    -1,    24,    25,    26,    27,
      28,    24,    25,    26,     1,    65,    66,    -1,    68,    37,
      -1,     1,     9,    -1,    42,    12,    13,    -1,    15,     9,
      -1,    -1,    12,    13,    14,    15,    16,    24,    25,    26,
      27,    28,    29,    30,    24,    25,    26,    65,    66,    -1,
      68,    -1,     1,    66,    41,    68,    -1,    37,    -1,    39,
       9,    -1,    42,    12,    13,    -1,    15,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    24,    25,    26,    65,    66,
      -1,    68,     1,    -1,    -1,    65,    66,    -1,    68,    -1,
       9,    -1,    -1,    12,    13,    14,    15,    16,    -1,    -1,
      -1,     1,    -1,    -1,    -1,    24,    25,    26,    -1,     9,
      -1,    -1,    12,    13,    14,    15,    16,    66,    37,    68,
      39,     1,    -1,    42,    24,    25,    26,    -1,    -1,     9,
      -1,    -1,    -1,    -1,    -1,    -1,    16,    37,    -1,    39,
      -1,    -1,    42,     1,    -1,    -1,    65,    66,     1,    68,
      -1,     9,    -1,    -1,    -1,    -1,     9,    37,    16,    12,
      13,    -1,    15,    -1,    -1,    65,    66,    47,    68,    -1,
       1,    24,    25,    26,    27,    28,    29,    30,     9,    37,
      -1,    12,    13,    -1,    15,    16,    -1,    -1,    41,    47,
      -1,    -1,    -1,    24,    25,    26,    -1,    -1,    -1,    -1,
      -1,    -1,     1,    -1,    -1,    -1,    37,    -1,     1,    -1,
       9,    42,    65,    66,    -1,    68,     9,    16,    -1,    12,
      13,    -1,    15,    16,    -1,    -1,    -1,    -1,     1,    -1,
      -1,    24,    25,    26,    65,    66,     9,    68,    37,    12,
      13,    -1,    15,    16,    37,    -1,    -1,    -1,    47,    42,
      -1,    24,    25,    26,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    37,    -1,     1,    -1,    -1,    42,
      -1,    -1,    65,    66,     9,    68,    -1,    12,    13,    -1,
      15,    16,    -1,    -1,    -1,    -1,     1,    -1,    -1,    24,
      25,    26,    65,    66,     9,    68,    -1,    12,    13,    -1,
      15,    -1,    37,    -1,    -1,    -1,    -1,    42,    -1,    24,
      25,    26,    27,    28,     1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,     9,    -1,    -1,    12,    13,    -1,    15,    -1,
      65,    66,    -1,    68,     1,    -1,    -1,    24,    25,    26,
      27,    28,     9,    -1,    -1,    12,    13,    -1,    15,    -1,
      65,    66,    -1,    68,     1,    -1,     1,    24,    25,    26,
      27,    28,     9,    -1,     9,    -1,    13,     1,    13,    16,
      -1,    16,    -1,    -1,    -1,     9,    -1,    -1,    65,    66,
      -1,    68,    16,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      37,    -1,    37,    40,    41,    42,    41,    42,    65,    66,
      47,    68,    47,    37,     1,    -1,    40,    41,    42,    56,
      -1,    56,     9,    47,    -1,     1,     1,     1,    -1,    16,
      -1,    -1,    56,     9,     9,     9,    -1,    -1,     1,    -1,
      16,    16,    16,    -1,    -1,    -1,     9,    -1,    -1,     1,
      37,    -1,    -1,    16,    41,    42,    -1,     9,    -1,    -1,
      47,    37,    37,    37,    16,    41,    42,    42,    42,    56,
      -1,    47,    47,    47,    37,    -1,    -1,    -1,    -1,    42,
      56,    56,    56,     1,    47,    37,     1,    -1,    -1,    -1,
      42,     9,    -1,    56,     9,    47,    -1,    -1,    16,     1,
      -1,    16,    -1,     1,    56,    -1,    -1,     9,    -1,    -1,
      -1,     9,    -1,    -1,    16,     1,    -1,    -1,    16,    37,
      -1,    -1,    37,     9,    42,    -1,    -1,    42,     1,    47,
      16,    -1,    47,    -1,    -1,    37,     9,    -1,    56,    37,
      42,    56,    -1,    16,    42,    47,    -1,    -1,    -1,    47,
      -1,    37,     1,    -1,    56,    -1,    42,    -1,    56,    -1,
       9,    47,    -1,     1,    37,     1,    -1,    16,    -1,    42,
      56,     9,    -1,     9,    47,    -1,     1,    -1,    16,    -1,
      16,    -1,    -1,    56,     9,    -1,    -1,     1,    37,    -1,
      -1,    16,    -1,    42,    -1,     9,    -1,    -1,    47,    37,
       1,    37,    16,    -1,    42,    -1,    42,    56,     9,    47,
      -1,    47,    37,    -1,    -1,    16,    -1,    42,    56,    -1,
      56,    -1,    47,    37,     1,    -1,    -1,    -1,    42,    -1,
       1,    56,     9,    47,    -1,    -1,    37,    -1,     9,    16,
      -1,    42,    56,    -1,    -1,    16,    47,    -1,     1,    -1,
      -1,    -1,    -1,    -1,     1,    56,     9,    -1,    -1,    -1,
      37,    -1,     9,    16,    -1,    42,    37,    -1,    -1,    16,
      47,    42,     1,    -1,    -1,    -1,    47,    -1,     1,    56,
       9,    -1,    -1,    -1,    37,    56,     9,    16,    -1,    42,
      37,    -1,    -1,    16,    47,    42,     1,    -1,    -1,    -1,
      47,    -1,     1,    56,     9,    -1,    -1,    -1,    37,    56,
       9,    16,    -1,    42,    37,    -1,    -1,    16,    47,    42,
       1,    -1,    -1,    -1,    47,    -1,     1,    56,     9,    -1,
      -1,    -1,    37,    56,     9,    16,    -1,    42,    37,    -1,
      -1,    16,    47,    42,     1,    -1,    -1,    -1,    47,    -1,
       1,    56,     9,    -1,    -1,     1,    37,    56,     9,    16,
      -1,    42,    37,     9,    -1,    16,    47,    42,     1,     1,
      16,    -1,    47,    -1,     1,    56,     9,     9,    -1,    -1,
      37,    56,     9,    16,    16,    42,    37,     1,    -1,    16,
      47,    37,     1,    -1,    -1,     9,    47,    -1,     1,    56,
       9,    47,    16,     1,    37,    37,     9,    16,    -1,     1,
      37,     9,    -1,    16,    47,    47,    -1,     9,    16,    -1,
      47,     1,     1,    37,    16,    -1,    -1,     1,    37,     9,
       9,    -1,    -1,    47,    37,     9,    16,    16,    47,    37,
      -1,    -1,    16,    -1,    47,    37,     1,    -1,    -1,    47,
      -1,     1,    -1,    -1,     9,    47,    -1,    37,    37,     9,
      -1,    16,     1,    37,     1,    -1,    16,    47,    47,    -1,
       9,    -1,     9,    47,    -1,     1,     1,    16,     1,    16,
       1,     1,    37,     9,     9,    -1,     9,    37,     9,     9,
      16,    16,    47,    16,     1,    16,    16,    47,    37,    -1,
      37,    -1,     9,    -1,    -1,     1,    -1,    -1,    47,    16,
      47,    37,    37,     9,    37,    -1,    37,    37,    -1,    -1,
      16,    47,    47,     1,    47,    -1,    47,    47,     1,     1,
      37,     9,    -1,    -1,    -1,    -1,     9,     9,    16,    -1,
      47,    37,    -1,    16,    16,    -1,    -1,    -1,    -1,    -1,
      -1,    47,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    37,
      -1,    -1,    -1,    -1,    37,    37,    -1,    -1,    -1,    47,
      -1,    -1,    -1,    -1,    47,    47
  };

  /* STOS_[STATE-NUM] -- The (internal number of the) accessing
     symbol of state STATE-NUM.  */
  const unsigned char
  mcmas_parser::yystos_[] =
  {
         0,     1,     3,    64,    75,    76,    77,    78,    80,   105,
     106,   108,    17,     1,    17,    15,     0,     1,    77,     1,
       4,    18,    19,    32,    81,    83,    88,    90,    92,    94,
     113,   115,     1,     3,   105,     1,    43,   108,   164,   166,
      72,    62,    63,    10,    15,    39,     1,    15,     1,    39,
       1,    39,     1,    39,     1,     7,    72,    82,    84,    85,
       1,    90,    94,   115,     1,     7,    84,    89,     1,    94,
     115,     1,     7,     8,    21,    22,    27,    38,    67,    72,
      73,    87,    93,    96,   133,   135,   136,   137,   138,   139,
     140,   141,   159,   160,     1,   115,     1,    11,    72,   114,
     117,     1,     5,   118,   120,   166,     1,    72,   167,     1,
      44,   169,   171,     1,    36,    88,    91,   109,   111,    42,
      42,     1,    10,    10,     1,    10,    18,     1,    18,     1,
      39,     1,    82,    85,     1,    42,    39,    94,   115,   115,
     120,    19,     1,    19,     1,    89,    39,   115,   120,     1,
      32,    73,   133,   135,   138,   141,     1,    32,   133,   135,
     138,    73,   133,     1,     8,   141,     1,    93,     1,    16,
      37,    42,     1,    27,    28,     1,    29,    30,     1,    12,
      13,    15,    24,    25,    26,    66,    68,   157,     1,    65,
     120,    42,     1,    42,     1,    40,   114,    39,     1,    39,
       1,     7,    35,   119,   122,   126,   128,   133,     1,     6,
      98,   100,   171,     1,    14,     1,     7,    72,   165,     1,
       8,    17,    38,    72,   172,     1,    34,    45,    46,   173,
     175,   181,   183,   189,   191,    10,    15,    39,     1,    15,
       1,    84,     1,    92,    95,   113,   116,     1,    11,    72,
     110,   112,     1,    91,     1,    20,    72,    86,    87,     1,
      10,    20,    87,     1,    42,   115,   120,   120,   100,   120,
     100,     1,     9,     9,     9,     1,     9,     1,     9,     1,
       9,     1,     1,   138,   138,   133,   133,   133,     1,     8,
     136,   136,   136,   137,   137,   137,   139,   139,   139,   138,
     140,   140,   100,    72,    72,     1,     5,    39,   124,     1,
       5,     1,   124,     1,   119,   126,   128,     1,   119,     1,
     124,    39,     1,    39,     1,     7,     8,    72,    99,   101,
     102,   103,     1,     7,    79,   175,   183,   191,     1,     8,
      17,    38,    67,    72,    87,   146,   147,   148,   149,   153,
     154,   155,   160,   162,   168,   168,    43,     1,    43,     1,
      14,    41,    72,   172,   172,     1,    41,   172,     1,    41,
       1,    16,    37,    42,   170,     1,     7,    72,   174,   178,
       1,   183,   191,     1,     7,     8,    17,    38,    48,    49,
      50,    51,    52,    53,    54,    55,    57,    58,    59,    60,
      61,    72,   182,   184,   188,     1,   191,     1,     8,    12,
      17,    38,    48,    49,    50,    51,    52,    53,    54,    55,
      57,    58,    59,    60,    61,    72,   192,   193,   197,     1,
      10,    10,     1,    10,    89,     1,     8,    17,    38,    67,
      72,    87,    93,    97,   134,   142,   143,   144,   145,   150,
     151,   152,   160,   161,     1,   116,     1,   117,     1,   118,
     121,    42,     1,    42,     1,    40,   110,    95,   116,    73,
       1,    11,    40,     1,    23,     1,    86,     1,    23,   120,
     100,   100,    79,   100,    79,   135,   135,    79,    10,     1,
      10,     1,    72,   129,   129,   119,   129,     6,     1,     6,
       1,   103,    15,     1,    99,   102,    14,    16,     3,     1,
       3,   183,   191,   191,    41,   146,   149,   153,   168,   146,
     153,   168,     1,    41,   168,     1,     8,   149,     1,    41,
       1,    66,    68,   157,     1,    65,     1,    27,    28,     1,
      29,    30,     1,    16,    37,    42,     1,    42,   168,   168,
      72,     1,    15,     1,     9,     1,     9,    72,    72,     1,
      72,    72,     7,    44,   172,   172,   172,     1,     7,    45,
       1,    45,     1,    15,   176,     1,    72,   174,   191,     1,
       8,    34,   186,   187,   188,     1,    34,     1,   188,    41,
     188,   188,   188,   188,   188,   188,   188,     1,     8,   185,
     185,     1,     8,   186,     1,     8,   187,   187,   186,   187,
       1,    41,     1,   182,   188,     1,    16,    37,    42,    47,
       1,     8,    72,   195,   196,   197,     1,   197,    72,    41,
     197,   197,   197,   197,   197,   197,   197,     1,     8,   194,
     194,     1,     8,   195,     1,     8,   196,   196,   195,   196,
       1,    41,     1,     7,   190,   197,     1,    69,    70,    71,
     194,     1,    16,    37,    42,    47,     1,    41,   134,   142,
     145,   150,   134,   142,   150,     1,    41,   134,     1,     8,
     145,    93,     1,    16,    37,    42,     1,    66,    68,   157,
       1,    65,     1,    27,    28,     1,    29,    30,   121,   114,
       1,   123,   127,   128,   134,     1,    98,   130,    72,    72,
     116,   121,    72,    72,     1,    87,    87,     1,    11,    87,
      87,   100,    79,    79,    79,     1,    11,    40,   125,   125,
     125,     9,   138,     1,     8,    31,    38,    72,   138,   156,
     103,   191,    72,     9,     9,     1,     9,     1,     9,     1,
       9,     1,     9,    72,    72,     1,     1,   146,   146,    72,
      72,   147,   147,   147,   146,   148,   148,     1,     8,   154,
     154,   154,   155,   155,   155,   168,   168,   168,     1,    42,
       1,    42,     1,    72,    87,   160,   163,    72,   163,     1,
      15,     1,    15,     1,    15,     1,    15,     1,    44,    44,
       1,    44,    10,     1,    10,     1,    17,    72,   179,   180,
     176,    17,    72,    17,    72,     1,     9,     1,     9,    32,
      33,     1,   188,   188,    17,    72,    17,    72,    72,    72,
      32,    33,     1,    32,    33,     1,    42,   188,   188,   188,
     188,    17,    72,    17,    72,    13,     1,     9,     1,     9,
       1,    13,    32,    33,     1,   197,   197,    17,    72,    17,
      72,    72,    72,    32,    33,     1,    32,    33,    46,     1,
      46,     1,    42,   197,   197,   197,   197,   197,   197,   197,
     197,    72,     1,     9,     9,     9,     1,     9,     1,     9,
       1,     9,    72,    72,     1,     1,   142,   142,   134,   134,
     134,   143,   143,   143,   142,   144,   144,     1,     8,   151,
     151,   151,   152,   152,   152,   130,     1,     1,   119,   127,
     128,   119,     1,   124,     1,     8,    72,   104,   131,   132,
       1,     7,   107,   121,   130,    79,    42,    72,     1,    42,
      72,    15,    72,   138,   156,   138,   156,     1,    15,   156,
       1,    41,   157,     1,    16,    37,    42,   153,   153,   163,
     163,   163,   163,    17,    72,   163,   163,   163,   163,    17,
      72,   163,     1,    11,    40,   177,   179,     1,    40,     1,
      40,     1,    40,     1,    40,     1,    56,     1,    56,     1,
      40,     1,    40,     1,    40,     1,    40,     1,    40,     1,
      40,     1,    40,     1,    40,     1,    56,     1,    56,     1,
      40,     1,    40,     1,    40,     1,    40,   150,   150,   107,
     119,   129,     1,   104,    15,     1,    14,    16,     1,    99,
     132,     3,     1,     3,   130,   107,    72,     1,     9,     1,
       9,    72,    72,    15,    31,    72,     1,    31,   138,   156,
     156,   156,    41,    41,    41,    41,     1,    42,   180,     1,
      42,   180,   177,   188,   188,   188,   188,   188,   188,   188,
     188,   188,   188,   188,   188,   188,   188,   188,   188,   188,
     188,   188,   188,   197,   197,   197,   197,   197,   197,   197,
     197,   197,   197,   197,   197,   197,   197,   197,   197,   197,
     197,   197,   197,   125,     9,   142,     1,     8,    17,    31,
      38,    72,   142,   158,   158,   104,   107,    72,     1,    15,
      15,    72,     1,    15,    72,    72,    72,    72,     1,     9,
       1,     9,     1,     9,     1,     9,     1,     9,     1,     9,
       1,     9,     1,     9,     1,     9,     1,     9,     1,     9,
       1,     9,     1,     9,     1,     9,     1,     9,     1,     9,
       1,     9,     1,     9,     1,     9,     1,     9,     1,     9,
       1,     9,     1,     9,     1,     9,     1,     9,     1,     9,
       1,     9,     1,     9,     1,     9,     1,     9,     1,     9,
       1,     9,     1,     9,     1,     9,     1,     9,     1,     9,
       1,     9,     1,     9,     1,     9,     1,     9,    15,    72,
     142,   158,   142,   158,     1,    41,     1,    15,   158,     1,
      41,   157,     1,    16,    37,    42,     1,    42,    72,    72,
      72,    72,    72,    72,     1,     9,     1,     9,    15,    31,
      72,     1,    31,    72,    72,     1,    15,    31,    72,     1,
      31,   142,   158,   158,   158,    72,     1,    15,    72,     1,
      15,    72,     1,    15,    15,    72,     1,    15,    72,    72,
      72,    72,    72,    72,    72,    72,    72
  };

#if YYDEBUG
  /* TOKEN_NUMBER_[YYLEX-NUM] -- Internal symbol number corresponding
     to YYLEX-NUM.  */
  const unsigned short int
  mcmas_parser::yytoken_number_[] =
  {
         0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,   289,   290,   291,   292,   293,   294,
     295,   296,   297,   298,   299,   300,   301,   302,   303,   304,
     305,   306,   307,   308,   309,   310,   311,   312,   313,   314,
     315,   316,   317,   318,   319,   320,   321,   322,   323,   324,
     325,   326,   327,   328
  };
#endif

  /* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
  const unsigned char
  mcmas_parser::yyr1_[] =
  {
         0,    74,    75,    75,    76,    76,    76,    77,    77,    77,
      77,    77,    77,    77,    77,    78,    78,    78,    78,    79,
      79,    79,    79,    80,    80,    80,    80,    80,    80,    80,
      80,    80,    81,    81,    81,    81,    82,    82,    82,    82,
      83,    83,    84,    84,    84,    84,    84,    85,    85,    85,
      85,    85,    85,    85,    85,    85,    85,    85,    85,    86,
      86,    86,    86,    87,    87,    87,    87,    88,    88,    88,
      88,    89,    89,    89,    89,    90,    90,    90,    91,    91,
      92,    92,    92,    92,    93,    93,    93,    93,    94,    94,
      94,    95,    95,    95,    96,    96,    96,    97,    97,    97,
      98,    98,    98,    98,    99,    99,    99,    99,   100,   100,
     101,   101,   101,   102,   102,   103,   103,   103,   103,   104,
     104,   104,   104,   105,   105,   105,   106,   106,   107,   107,
     107,   107,   108,   108,   108,   108,   108,   109,   109,   109,
     109,   109,   109,   109,   109,   110,   110,   110,   110,   111,
     111,   111,   112,   112,   112,   112,   113,   113,   113,   113,
     113,   113,   113,   113,   114,   114,   114,   114,   115,   115,
     115,   116,   116,   117,   117,   117,   117,   118,   118,   118,
     118,   119,   119,   119,   119,   120,   120,   120,   120,   120,
     121,   121,   121,   121,   122,   122,   122,   123,   123,   123,
     124,   124,   124,   124,   125,   125,   125,   125,   126,   126,
     127,   127,   128,   128,   129,   129,   129,   129,   130,   130,
     131,   131,   131,   132,   132,   132,   132,   132,   133,   133,
     133,   133,   133,   133,   133,   133,   133,   133,   133,   134,
     134,   134,   134,   134,   134,   134,   134,   134,   134,   134,
     135,   135,   135,   135,   136,   136,   136,   136,   137,   137,
     137,   137,   138,   138,   138,   138,   139,   139,   139,   140,
     140,   140,   141,   141,   141,   141,   142,   142,   142,   142,
     143,   143,   143,   144,   144,   144,   145,   145,   145,   145,
     146,   146,   146,   146,   147,   147,   147,   148,   148,   148,
     149,   149,   149,   149,   150,   150,   150,   150,   151,   151,
     151,   151,   152,   152,   152,   152,   153,   153,   153,   153,
     154,   154,   154,   154,   155,   155,   155,   155,   156,   156,
     156,   156,   156,   156,   156,   156,   156,   156,   156,   156,
     156,   156,   156,   156,   156,   156,   156,   156,   156,   156,
     156,   157,   157,   157,   157,   157,   157,   158,   158,   158,
     158,   158,   158,   158,   158,   158,   158,   158,   158,   158,
     158,   158,   158,   158,   158,   158,   158,   158,   158,   158,
     158,   158,   158,   158,   158,   158,   158,   159,   159,   159,
     160,   160,   161,   161,   161,   161,   161,   161,   162,   162,
     162,   162,   162,   162,   162,   162,   163,   163,   163,   164,
     165,   165,   165,   165,   166,   166,   167,   167,   167,   167,
     167,   167,   167,   167,   167,   168,   168,   168,   168,   168,
     168,   168,   168,   168,   168,   168,   169,   169,   170,   170,
     170,   170,   170,   170,   170,   170,   171,   171,   172,   172,
     172,   172,   172,   172,   172,   172,   172,   172,   172,   172,
     172,   172,   172,   172,   172,   172,   172,   172,   172,   172,
     172,   172,   172,   173,   173,   174,   174,   174,   174,   175,
     175,   175,   176,   176,   176,   176,   177,   177,   177,   177,
     178,   178,   178,   179,   179,   179,   179,   180,   180,   180,
     181,   181,   182,   182,   182,   182,   183,   183,   184,   184,
     184,   184,   184,   185,   185,   185,   185,   185,   185,   185,
     185,   186,   186,   186,   186,   186,   186,   186,   186,   186,
     186,   186,   186,   186,   186,   186,   186,   187,   187,   187,
     187,   187,   187,   187,   187,   188,   188,   188,   188,   188,
     188,   188,   188,   188,   188,   188,   188,   188,   188,   188,
     188,   188,   188,   188,   188,   188,   188,   188,   188,   188,
     188,   188,   188,   188,   188,   188,   188,   188,   188,   189,
     189,   190,   190,   190,   190,   191,   192,   192,   192,   192,
     192,   193,   193,   193,   194,   194,   194,   194,   194,   194,
     194,   194,   195,   195,   195,   195,   195,   195,   195,   195,
     195,   195,   195,   195,   195,   195,   195,   195,   196,   196,
     196,   196,   196,   196,   196,   196,   197,   197,   197,   197,
     197,   197,   197,   197,   197,   197,   197,   197,   197,   197,
     197,   197,   197,   197,   197,   197,   197,   197,   197,   197,
     197,   197,   197,   197,   197,   197,   197,   197,   197,   197,
     197,   197,   197,   197,   197
  };

  /* YYR2[YYN] -- Number of symbols composing right hand side of rule YYN.  */
  const unsigned char
  mcmas_parser::yyr2_[] =
  {
         0,     2,     1,     2,     4,     4,     1,     7,     6,     6,
       5,     6,     5,     5,     4,     2,     2,     2,     1,     2,
       2,     2,     1,     8,     7,     7,     6,     7,     6,     6,
       5,     1,     2,     2,     2,     1,     2,     2,     2,     1,
       3,     2,     2,     2,     3,     3,     1,     3,     3,     3,
       5,     5,     5,     5,     5,     4,     5,     4,     1,     1,
       3,     3,     1,     1,     2,     2,     1,     2,     2,     2,
       1,     2,     2,     2,     1,     3,     2,     1,     3,     1,
       2,     2,     2,     1,     2,     2,     2,     1,     3,     2,
       1,     3,     2,     1,     2,     2,     1,     2,     2,     1,
       2,     2,     2,     1,     2,     2,     2,     1,     3,     2,
       1,     2,     1,     4,     1,     3,     3,     3,     1,     3,
       3,     3,     1,     1,     2,     1,     1,     1,     2,     2,
       2,     1,     8,     7,     9,     8,     1,     3,     3,     3,
       3,     2,     2,     3,     1,     2,     2,     2,     1,     3,
       2,     1,     1,     3,     3,     1,     3,     3,     3,     3,
       2,     2,     3,     1,     2,     2,     2,     1,     3,     2,
       1,     3,     1,     1,     3,     3,     1,     2,     2,     2,
       1,     2,     2,     2,     1,     3,     4,     3,     2,     1,
       3,     4,     3,     1,     1,     2,     1,     1,     2,     1,
       2,     2,     2,     1,     2,     2,     2,     1,     4,     1,
       4,     1,     4,     4,     1,     3,     3,     1,     3,     1,
       1,     2,     1,     4,     4,     4,     4,     1,     3,     3,
       3,     3,     3,     3,     3,     2,     2,     3,     1,     3,
       3,     3,     3,     3,     3,     3,     2,     2,     3,     1,
       3,     3,     3,     1,     3,     3,     3,     1,     3,     3,
       3,     1,     3,     3,     3,     1,     3,     3,     1,     2,
       2,     1,     3,     3,     3,     1,     3,     3,     3,     1,
       3,     3,     1,     2,     2,     1,     3,     3,     3,     1,
       3,     3,     3,     1,     3,     3,     1,     2,     2,     1,
       3,     3,     3,     1,     3,     3,     3,     1,     3,     3,
       3,     1,     3,     3,     3,     1,     3,     3,     3,     1,
       3,     3,     3,     1,     3,     3,     3,     1,     3,     3,
       3,     3,     3,     3,     3,     2,     2,     3,     3,     3,
       3,     2,     5,     5,     5,     5,     4,     4,     5,     3,
       1,     1,     1,     1,     1,     1,     1,     3,     3,     3,
       3,     3,     3,     3,     2,     2,     3,     3,     3,     3,
       2,     5,     5,     5,     5,     4,     4,     5,     3,     5,
       5,     5,     4,     4,     5,     3,     1,     1,     1,     1,
       1,     1,     1,     1,     3,     3,     3,     1,     1,     1,
       3,     3,     3,     3,     3,     1,     1,     1,     1,     1,
       2,     2,     2,     1,     3,     1,     4,     4,     4,     4,
       5,     5,     5,     5,     1,     3,     3,     3,     3,     3,
       3,     3,     2,     2,     3,     1,     1,     1,     3,     3,
       3,     3,     2,     2,     3,     1,     3,     1,     3,     3,
       3,     3,     3,     3,     3,     2,     2,     7,     7,     7,
       5,     5,     5,     5,     7,     5,     5,     5,     5,     4,
       5,     4,     1,     1,     1,     2,     2,     2,     1,     3,
       2,     1,     2,     2,     2,     1,     2,     2,     2,     1,
       4,     5,     1,     1,     3,     3,     1,     1,     1,     1,
       1,     1,     2,     2,     2,     1,     2,     3,     2,     2,
       3,     3,     1,     5,     5,     5,     5,     5,     5,     5,
       5,     5,     5,     5,     5,     5,     5,     5,     5,     5,
       5,     5,     5,     5,     5,     5,     5,     5,     5,     5,
       5,     5,     5,     5,     5,     3,     3,     3,     3,     3,
       3,     3,     2,     2,     3,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       1,     3,     3,     3,     3,     3,     3,     3,     1,     1,
       1,     2,     2,     2,     1,     3,     2,     2,     3,     3,
       1,     3,     3,     3,     5,     5,     5,     5,     5,     5,
       5,     5,     5,     5,     5,     5,     5,     5,     5,     5,
       5,     5,     5,     5,     5,     5,     5,     5,     5,     5,
       5,     5,     5,     5,     5,     5,     3,     3,     3,     3,
       3,     3,     3,     2,     2,     3,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     3,     3,     3,     3,     2,     1,     3,     3,     3,
       3,     3,     3,     3,     1
  };

#if YYDEBUG || YYERROR_VERBOSE || YYTOKEN_TABLE
  /* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
     First, the terminals, then, starting at \a yyntokens_, nonterminals.  */
  const char*
  const mcmas_parser::yytname_[] =
  {
    "\"end of file\"", "error", "$undefined", "AGENT", "ACTIONS",
  "PROTOCOL", "EVOLUTION", "END", "LB", "RB", "LCB", "RCB", "LT", "GT",
  "IF", "EQ", "AND", "ENVIRONMENT", "OBSVARS", "VARS", "BOOLEAN", "BTRUE",
  "BFALSE", "TO", "LE", "GE", "NEQ", "MINUS", "PLUS", "TIMES", "DIVIDE",
  "ACTION", "REDSTATES", "GREENSTATES", "FAIRNESS", "OTHER", "LOBSVARS",
  "OR", "NOT", "COLON", "COMMA", "DOT", "SEMICOLON", "EVALUATION",
  "INITSTATES", "GROUPS", "FORMULAE", "IMPLIES", "AG", "EG", "AX", "EX",
  "AF", "EF", "A", "E", "UNTIL", "K", "GK", "GCK", "O", "DK",
  "MULTIASSIGNMENT", "SINGLEASSIGNMENT", "SEMANTICS", "BITAND", "BITOR",
  "BITNOT", "BITXOR", "X", "F", "G", "\"identifier\"", "\"number\"",
  "$accept", "eis", "semantics", "is", "envprefix", "envsuffix",
  "environment", "obsprefix", "obssuffix", "obsvardef", "varidlist",
  "onevardef", "enumlist", "integer", "varprefix", "varsuffix", "envardef",
  "vardef", "redprefix", "redsuffix", "enreddef", "reddef", "enrboolcond",
  "rboolcond", "evprefix", "evsuffix", "envevdef", "envevdeflist",
  "envevline", "boolresult", "boolresult1", "agents", "agprefix",
  "agsuffix", "agent", "lobsprefix", "lobssuffix", "lobsvarsdef",
  "lobsvaridlist", "actprefix", "actsuffix", "enactiondef", "actiondef",
  "actionidlist", "protprefix", "protsuffix", "enprotdef", "protdef",
  "enprotdeflist", "protdeflist", "plprefix", "plsuffix", "enprotline",
  "protline", "otherbranch", "enabledidlist", "evdef", "evdeflist",
  "evline", "enlboolcond", "lboolcond", "expr1", "term1", "element1",
  "expr4", "term4", "factor4", "element4", "expr5", "term5", "factor5",
  "element5", "expr6", "term6", "factor6", "element6", "expr2", "term2",
  "element2", "expr3", "term3", "element3", "eboolcond", "logicop",
  "gboolcond", "varvalue1", "boolvalue", "varvalue2", "varvalue3",
  "varvalue4", "evaprefix", "evasuffix", "evaluation", "evalist",
  "evaboolcond", "iniprefix", "inisuffix", "istates", "isboolcond",
  "groupprefix", "groupsuffix", "groups", "gplprefix", "gplsufffix",
  "groupdeflist", "namelist", "agentname", "fairprefix", "fairsuffix",
  "fairness", "fformlist", "untilprefixfair", "epistemicprefixfair",
  "gepistemicprefixfair", "fformula", "forprefix", "forsuffix", "formulae",
  "formlist", "atlprefix", "untilprefix", "epistemicprefix",
  "gepistemicprefix", "formula", 0
  };
#endif

#if YYDEBUG
  /* YYRHS -- A `-1'-separated list of the rules' RHS.  */
  const mcmas_parser::rhs_number_type
  mcmas_parser::yyrhs_[] =
  {
        75,     0,    -1,    77,    -1,    76,    77,    -1,    64,    15,
      62,    42,    -1,    64,    15,    63,    42,    -1,     1,    -1,
      80,   105,   166,   171,   175,   183,   191,    -1,    80,   105,
     166,   171,   175,   191,    -1,    80,   105,   166,   171,   183,
     191,    -1,    80,   105,   166,   171,   191,    -1,   105,   166,
     171,   175,   183,   191,    -1,   105,   166,   171,   175,   191,
      -1,   105,   166,   171,   183,   191,    -1,   105,   166,   171,
     191,    -1,     3,    17,    -1,     1,    17,    -1,     3,     1,
      -1,     1,    -1,     7,     3,    -1,     1,     3,    -1,     7,
       1,    -1,     1,    -1,    78,    83,    90,    94,   115,   120,
     100,    79,    -1,    78,    83,    90,   115,   120,   100,    79,
      -1,    78,    90,    94,   115,   120,   100,    79,    -1,    78,
      90,   115,   120,   100,    79,    -1,    78,    83,    94,   115,
     120,   100,    79,    -1,    78,    83,   115,   120,   100,    79,
      -1,    78,    94,   115,   120,   100,    79,    -1,    78,   115,
     120,   100,    79,    -1,     1,    -1,    18,    39,    -1,     1,
      39,    -1,    18,     1,    -1,     1,    -1,     7,    18,    -1,
       1,    18,    -1,     7,     1,    -1,     1,    -1,    81,    84,
      82,    -1,    81,    82,    -1,    85,    42,    -1,    85,     1,
      -1,    84,    85,    42,    -1,    84,    85,     1,    -1,     1,
      -1,    72,    39,    20,    -1,    72,    39,     1,    -1,    72,
       1,    20,    -1,    72,    39,    87,    23,    87,    -1,    72,
       1,    87,    23,    87,    -1,    72,    39,    87,     1,    87,
      -1,    72,     1,    87,     1,    87,    -1,    72,    39,    10,
      86,    11,    -1,    72,     1,    86,    11,    -1,    72,    39,
      10,    86,     1,    -1,    72,     1,    86,     1,    -1,     1,
      -1,    72,    -1,    86,    40,    72,    -1,    86,     1,    72,
      -1,     1,    -1,    73,    -1,    27,    73,    -1,     1,    73,
      -1,     1,    -1,    19,    39,    -1,     1,    39,    -1,    19,
       1,    -1,     1,    -1,     7,    19,    -1,     1,    19,    -1,
       7,     1,    -1,     1,    -1,    88,    84,    89,    -1,    88,
      89,    -1,     1,    -1,    88,    84,    89,    -1,     1,    -1,
      32,    39,    -1,    32,     1,    -1,     1,    39,    -1,     1,
      -1,     7,    32,    -1,     1,    32,    -1,     7,     1,    -1,
       1,    -1,    92,    96,    93,    -1,    92,    93,    -1,     1,
      -1,    92,    97,    93,    -1,    92,    93,    -1,     1,    -1,
     133,    42,    -1,   133,     1,    -1,     1,    -1,   134,    42,
      -1,   134,     1,    -1,     1,    -1,     6,    39,    -1,     1,
      39,    -1,     6,     1,    -1,     1,    -1,     7,     6,    -1,
       1,     6,    -1,     7,     1,    -1,     1,    -1,    98,   101,
      99,    -1,    98,    99,    -1,   102,    -1,   101,   102,    -1,
       1,    -1,   103,    14,   156,    42,    -1,     1,    -1,     8,
     103,     9,    -1,   103,    16,   103,    -1,    72,    15,   138,
      -1,     1,    -1,     8,   104,     9,    -1,   104,    16,   104,
      -1,    72,    15,   142,    -1,     1,    -1,   108,    -1,   105,
     108,    -1,     1,    -1,     3,    -1,     1,    -1,     7,     3,
      -1,     1,     3,    -1,     7,     1,    -1,     1,    -1,   106,
      72,    91,    95,   116,   121,   130,   107,    -1,   106,    72,
      91,   116,   121,   130,   107,    -1,   106,    72,   111,    91,
      95,   116,   121,   130,   107,    -1,   106,    72,   111,    91,
     116,   121,   130,   107,    -1,     1,    -1,    36,    15,    10,
      -1,     1,    15,    10,    -1,    36,     1,    10,    -1,    36,
      15,     1,    -1,     1,    10,    -1,    36,     1,    -1,     1,
      15,     1,    -1,     1,    -1,    11,    42,    -1,    11,     1,
      -1,     1,    42,    -1,     1,    -1,   109,   112,   110,    -1,
     109,   110,    -1,     1,    -1,    72,    -1,   112,    40,    72,
      -1,   112,     1,    72,    -1,     1,    -1,     4,    15,    10,
      -1,     1,    15,    10,    -1,     4,     1,    10,    -1,     4,
      15,     1,    -1,     1,    10,    -1,     4,     1,    -1,     1,
      15,     1,    -1,     1,    -1,    11,    42,    -1,    11,     1,
      -1,     1,    42,    -1,     1,    -1,   113,   117,   114,    -1,
     113,   114,    -1,     1,    -1,   113,   117,   114,    -1,     1,
      -1,    72,    -1,   117,    40,    72,    -1,   117,     1,    72,
      -1,     1,    -1,     5,    39,    -1,     1,    39,    -1,     5,
       1,    -1,     1,    -1,     7,     5,    -1,     1,     5,    -1,
       7,     1,    -1,     1,    -1,   118,   122,   119,    -1,   118,
     122,   128,   119,    -1,   118,   128,   119,    -1,   118,   119,
      -1,     1,    -1,   118,   123,   119,    -1,   118,   123,   128,
     119,    -1,   118,   128,   119,    -1,     1,    -1,   126,    -1,
     122,   126,    -1,     1,    -1,   127,    -1,   123,   127,    -1,
       1,    -1,    39,    10,    -1,     1,    10,    -1,    39,     1,
      -1,     1,    -1,    11,    42,    -1,     1,    42,    -1,    11,
       1,    -1,     1,    -1,   133,   124,   129,   125,    -1,     1,
      -1,   134,   124,   129,   125,    -1,     1,    -1,    35,   124,
     129,   125,    -1,     1,   124,   129,   125,    -1,    72,    -1,
     129,    40,    72,    -1,   129,     1,    72,    -1,     1,    -1,
      98,   131,    99,    -1,     1,    -1,   132,    -1,   131,   132,
      -1,     1,    -1,   104,    14,   158,    42,    -1,   104,     1,
     158,    42,    -1,   104,    14,   158,     1,    -1,   104,     1,
     158,     1,    -1,     1,    -1,     8,   133,     9,    -1,     1,
     133,     9,    -1,     8,   133,     1,    -1,     1,   133,     1,
      -1,   133,    16,   133,    -1,   133,    37,   133,    -1,   133,
       1,   133,    -1,    38,   133,    -1,     1,   133,    -1,   138,
     157,   138,    -1,     1,    -1,     8,   134,     9,    -1,     1,
     134,     9,    -1,     8,   134,     1,    -1,     1,   134,     1,
      -1,   134,    16,   134,    -1,   134,    37,   134,    -1,   134,
       1,   134,    -1,    38,   134,    -1,     1,   134,    -1,   142,
     157,   142,    -1,     1,    -1,   135,    28,   136,    -1,   135,
      27,   136,    -1,   135,     1,   136,    -1,   136,    -1,   136,
      29,   137,    -1,   136,    30,   137,    -1,   136,     1,   137,
      -1,   137,    -1,     8,   135,     9,    -1,     1,   135,     9,
      -1,     8,   135,     1,    -1,   159,    -1,   138,    66,   139,
      -1,   138,    68,   139,    -1,   138,     1,   139,    -1,   139,
      -1,   139,    65,   140,    -1,   139,     1,   140,    -1,   140,
      -1,    67,   141,    -1,     1,   141,    -1,   141,    -1,     8,
     138,     9,    -1,     1,   138,     9,    -1,     8,   138,     1,
      -1,   135,    -1,   142,    66,   143,    -1,   142,    68,   143,
      -1,   142,     1,   143,    -1,   143,    -1,   143,    65,   144,
      -1,   143,     1,   144,    -1,   144,    -1,    67,   145,    -1,
       1,   145,    -1,   145,    -1,     8,   142,     9,    -1,     1,
     142,     9,    -1,     8,   142,     1,    -1,   150,    -1,   146,
      66,   147,    -1,   146,    68,   147,    -1,   146,     1,   147,
      -1,   147,    -1,   147,    65,   148,    -1,   147,     1,   148,
      -1,   148,    -1,    67,   149,    -1,     1,   149,    -1,   149,
      -1,     8,   146,     9,    -1,     1,   146,     9,    -1,     8,
     146,     1,    -1,   153,    -1,   150,    28,   151,    -1,   150,
      27,   151,    -1,   150,     1,   151,    -1,   151,    -1,   151,
      29,   152,    -1,   151,    30,   152,    -1,   151,     1,   152,
      -1,   152,    -1,     8,   150,     9,    -1,     1,   150,     9,
      -1,     8,   150,     1,    -1,   161,    -1,   153,    28,   154,
      -1,   153,    27,   154,    -1,   153,     1,   154,    -1,   154,
      -1,   154,    29,   155,    -1,   154,    30,   155,    -1,   154,
       1,   155,    -1,   155,    -1,     8,   153,     9,    -1,     1,
     153,     9,    -1,     8,   153,     1,    -1,   162,    -1,     8,
     156,     9,    -1,     1,   156,     9,    -1,     8,   156,     1,
      -1,     1,   156,     1,    -1,   156,    16,   156,    -1,   156,
      37,   156,    -1,   156,     1,   156,    -1,    38,   156,    -1,
       1,   156,    -1,   138,   157,   138,    -1,    31,    15,    72,
      -1,     1,    15,    72,    -1,    31,     1,    72,    -1,     1,
      72,    -1,    72,    41,    31,    15,    72,    -1,    72,     1,
      31,    15,    72,    -1,    72,    41,     1,    15,    72,    -1,
      72,    41,    31,     1,    72,    -1,    72,     1,    15,    72,
      -1,    72,    41,     1,    72,    -1,    72,     1,    31,     1,
      72,    -1,    72,     1,    72,    -1,     1,    -1,    12,    -1,
      24,    -1,    13,    -1,    25,    -1,    15,    -1,    26,    -1,
       8,   158,     9,    -1,     1,   158,     9,    -1,     8,   158,
       1,    -1,     1,   158,     1,    -1,   158,    16,   158,    -1,
     158,    37,   158,    -1,   158,     1,   158,    -1,    38,   158,
      -1,     1,   158,    -1,   142,   157,   142,    -1,    31,    15,
      72,    -1,     1,    15,    72,    -1,    31,     1,    72,    -1,
       1,    72,    -1,    72,    41,    31,    15,    72,    -1,    72,
       1,    31,    15,    72,    -1,    72,    41,     1,    15,    72,
      -1,    72,    41,    31,     1,    72,    -1,    72,     1,    15,
      72,    -1,    72,    41,     1,    72,    -1,    72,     1,    31,
       1,    72,    -1,    72,     1,    72,    -1,    17,    41,    31,
      15,    72,    -1,    17,    41,     1,    15,    72,    -1,    17,
      41,    31,     1,    72,    -1,    17,     1,    15,    72,    -1,
      17,    41,     1,    72,    -1,    17,     1,    31,     1,    72,
      -1,    17,     1,    72,    -1,     1,    -1,   160,    -1,    72,
      -1,    87,    -1,    21,    -1,    22,    -1,   160,    -1,    72,
      -1,    17,    41,    72,    -1,     1,    41,    72,    -1,    17,
       1,    72,    -1,    87,    -1,   160,    -1,    72,    -1,    72,
      41,    72,    -1,    72,     1,    72,    -1,    17,    41,    72,
      -1,     1,    41,    72,    -1,    17,     1,    72,    -1,    87,
      -1,   160,    -1,    72,    -1,    87,    -1,    43,    -1,     7,
      43,    -1,     1,    43,    -1,     7,     1,    -1,     1,    -1,
     164,   167,   165,    -1,     1,    -1,    72,    14,   168,    42,
      -1,    72,     1,   168,    42,    -1,    72,    14,   168,     1,
      -1,    72,     1,   168,     1,    -1,   167,    72,    14,   168,
      42,    -1,   167,    72,     1,   168,    42,    -1,   167,    72,
      14,   168,     1,    -1,   167,    72,     1,   168,     1,    -1,
       1,    -1,     8,   168,     9,    -1,     1,   168,     9,    -1,
       8,   168,     1,    -1,     1,   168,     1,    -1,   168,    16,
     168,    -1,   168,    37,   168,    -1,   168,     1,   168,    -1,
      38,   168,    -1,     1,   168,    -1,   146,   157,   146,    -1,
       1,    -1,    44,    -1,     1,    -1,    42,     7,    44,    -1,
       1,     7,    44,    -1,    42,     1,    44,    -1,    42,     7,
       1,    -1,     1,    44,    -1,    42,     1,    -1,     1,     7,
       1,    -1,     1,    -1,   169,   172,   170,    -1,     1,    -1,
       8,   172,     9,    -1,     1,   172,     9,    -1,     8,   172,
       1,    -1,     1,   172,     1,    -1,   172,    16,   172,    -1,
     172,    37,   172,    -1,   172,     1,   172,    -1,    38,   172,
      -1,     1,   172,    -1,    72,    41,    72,    15,    72,    41,
      72,    -1,    72,    41,    72,    15,    17,    41,    72,    -1,
      17,    41,    72,    15,    72,    41,    72,    -1,    72,    41,
      72,    15,   163,    -1,    72,     1,    72,    15,   163,    -1,
      72,    41,    72,     1,   163,    -1,    72,     1,    72,     1,
     163,    -1,    17,    41,    72,    15,    17,    41,    72,    -1,
      17,    41,    72,    15,   163,    -1,    17,     1,    72,    15,
     163,    -1,    17,    41,    72,     1,   163,    -1,    17,     1,
      72,     1,   163,    -1,     1,    72,    15,   163,    -1,     1,
      41,    72,     1,   163,    -1,     1,    72,     1,   163,    -1,
       1,    -1,    45,    -1,     1,    -1,     7,    45,    -1,     1,
      45,    -1,     7,     1,    -1,     1,    -1,   173,   178,   174,
      -1,   173,   174,    -1,     1,    -1,    15,    10,    -1,     1,
      10,    -1,    15,     1,    -1,     1,    -1,    11,    42,    -1,
       1,    42,    -1,    11,     1,    -1,     1,    -1,    72,   176,
     179,   177,    -1,   178,    72,   176,   179,   177,    -1,     1,
      -1,   180,    -1,   179,    40,   180,    -1,   179,     1,   180,
      -1,     1,    -1,    17,    -1,    72,    -1,     1,    -1,    34,
      -1,     1,    -1,     7,    34,    -1,     1,    34,    -1,     7,
       1,    -1,     1,    -1,   181,   182,    -1,   181,   184,   182,
      -1,   188,    42,    -1,   188,     1,    -1,   184,   188,    42,
      -1,   184,   188,     1,    -1,     1,    -1,     8,   188,    56,
     188,     9,    -1,     1,   188,    56,   188,     9,    -1,     8,
     188,     1,   188,     9,    -1,     8,   188,    56,   188,     1,
      -1,     1,   188,     1,   188,     9,    -1,     1,   188,    56,
     188,     1,    -1,     8,   188,     1,   188,     1,    -1,     1,
     188,     1,   188,     1,    -1,     8,    72,    40,   188,     9,
      -1,     1,    72,    40,   188,     9,    -1,     8,    72,     1,
     188,     9,    -1,     8,    72,    40,   188,     1,    -1,     1,
      72,     1,   188,     9,    -1,     1,    72,    40,   188,     1,
      -1,     8,    72,     1,   188,     1,    -1,     1,    72,     1,
     188,     1,    -1,     8,    17,    40,   188,     9,    -1,     1,
      17,    40,   188,     9,    -1,     8,    17,     1,   188,     9,
      -1,     8,    17,    40,   188,     1,    -1,     1,    17,     1,
     188,     9,    -1,     1,    17,    40,   188,     1,    -1,     8,
      17,     1,   188,     1,    -1,     1,    17,     1,   188,     1,
      -1,     8,    72,    40,   188,     9,    -1,     1,    72,    40,
     188,     9,    -1,     8,    72,     1,   188,     9,    -1,     8,
      72,    40,   188,     1,    -1,     1,    72,     1,   188,     9,
      -1,     1,    72,    40,   188,     1,    -1,     8,    72,     1,
     188,     1,    -1,     1,    72,     1,   188,     1,    -1,     8,
     188,     9,    -1,     1,   188,     9,    -1,     8,   188,     1,
      -1,     1,   188,     1,    -1,   188,    16,   188,    -1,   188,
      37,   188,    -1,   188,     1,   188,    -1,    38,   188,    -1,
       1,   188,    -1,   188,    47,   188,    -1,    48,   188,    -1,
      49,   188,    -1,    50,   188,    -1,    51,   188,    -1,    52,
     188,    -1,    53,   188,    -1,    54,   185,    -1,    55,   185,
      -1,    57,   186,    -1,    58,   187,    -1,    59,   187,    -1,
      60,   186,    -1,    61,   187,    -1,     1,   186,    -1,     1,
     187,    -1,    72,    -1,    72,    41,    33,    -1,    72,    41,
      32,    -1,    17,    41,    33,    -1,    17,    41,    32,    -1,
      72,    41,     1,    -1,    72,     1,    33,    -1,    72,     1,
      32,    -1,     1,    -1,    46,    -1,     1,    -1,     7,    46,
      -1,     1,    46,    -1,     7,     1,    -1,     1,    -1,   189,
     192,   190,    -1,   197,    42,    -1,   197,     1,    -1,   192,
     197,    42,    -1,   192,   197,     1,    -1,     1,    -1,    12,
      72,    13,    -1,    12,    72,     1,    -1,     1,    72,    13,
      -1,     8,   197,    56,   197,     9,    -1,     1,   197,    56,
     197,     9,    -1,     8,   197,     1,   197,     9,    -1,     8,
     197,    56,   197,     1,    -1,     1,   197,     1,   197,     9,
      -1,     1,   197,    56,   197,     1,    -1,     8,   197,     1,
     197,     1,    -1,     1,   197,     1,   197,     1,    -1,     8,
      72,    40,   197,     9,    -1,     1,    72,    40,   197,     9,
      -1,     8,    72,     1,   197,     9,    -1,     8,    72,    40,
     197,     1,    -1,     1,    72,     1,   197,     9,    -1,     1,
      72,    40,   197,     1,    -1,     8,    72,     1,   197,     1,
      -1,     1,    72,     1,   197,     1,    -1,     8,    17,    40,
     197,     9,    -1,     1,    17,    40,   197,     9,    -1,     8,
      17,     1,   197,     9,    -1,     8,    17,    40,   197,     1,
      -1,     1,    17,     1,   197,     9,    -1,     1,    17,    40,
     197,     1,    -1,     8,    17,     1,   197,     1,    -1,     1,
      17,     1,   197,     1,    -1,     8,    72,    40,   197,     9,
      -1,     1,    72,    40,   197,     9,    -1,     8,    72,     1,
     197,     9,    -1,     8,    72,    40,   197,     1,    -1,     1,
      72,     1,   197,     9,    -1,     1,    72,    40,   197,     1,
      -1,     8,    72,     1,   197,     1,    -1,     1,    72,     1,
     197,     1,    -1,     8,   197,     9,    -1,     1,   197,     9,
      -1,     8,   197,     1,    -1,     1,   197,     1,    -1,   197,
      16,   197,    -1,   197,    37,   197,    -1,   197,     1,   197,
      -1,    38,   197,    -1,     1,   197,    -1,   197,    47,   197,
      -1,    48,   197,    -1,    49,   197,    -1,    50,   197,    -1,
      51,   197,    -1,    52,   197,    -1,    53,   197,    -1,    54,
     194,    -1,    55,   194,    -1,    57,   195,    -1,    58,   196,
      -1,    59,   196,    -1,    60,   195,    -1,    61,   196,    -1,
       1,   195,    -1,     1,   196,    -1,   193,    69,   197,    -1,
     193,    70,   197,    -1,   193,    71,   197,    -1,   193,     1,
     197,    -1,   193,   194,    -1,    72,    -1,    72,    41,    33,
      -1,    72,    41,    32,    -1,    17,    41,    33,    -1,    17,
      41,    32,    -1,    72,    41,     1,    -1,    72,     1,    33,
      -1,    72,     1,    32,    -1,     1,    -1
  };

  /* YYPRHS[YYN] -- Index of the first RHS symbol of rule number YYN in
     YYRHS.  */
  const unsigned short int
  mcmas_parser::yyprhs_[] =
  {
         0,     0,     3,     5,     8,    13,    18,    20,    28,    35,
      42,    48,    55,    61,    67,    72,    75,    78,    81,    83,
      86,    89,    92,    94,   103,   111,   119,   126,   134,   141,
     148,   154,   156,   159,   162,   165,   167,   170,   173,   176,
     178,   182,   185,   188,   191,   195,   199,   201,   205,   209,
     213,   219,   225,   231,   237,   243,   248,   254,   259,   261,
     263,   267,   271,   273,   275,   278,   281,   283,   286,   289,
     292,   294,   297,   300,   303,   305,   309,   312,   314,   318,
     320,   323,   326,   329,   331,   334,   337,   340,   342,   346,
     349,   351,   355,   358,   360,   363,   366,   368,   371,   374,
     376,   379,   382,   385,   387,   390,   393,   396,   398,   402,
     405,   407,   410,   412,   417,   419,   423,   427,   431,   433,
     437,   441,   445,   447,   449,   452,   454,   456,   458,   461,
     464,   467,   469,   478,   486,   496,   505,   507,   511,   515,
     519,   523,   526,   529,   533,   535,   538,   541,   544,   546,
     550,   553,   555,   557,   561,   565,   567,   571,   575,   579,
     583,   586,   589,   593,   595,   598,   601,   604,   606,   610,
     613,   615,   619,   621,   623,   627,   631,   633,   636,   639,
     642,   644,   647,   650,   653,   655,   659,   664,   668,   671,
     673,   677,   682,   686,   688,   690,   693,   695,   697,   700,
     702,   705,   708,   711,   713,   716,   719,   722,   724,   729,
     731,   736,   738,   743,   748,   750,   754,   758,   760,   764,
     766,   768,   771,   773,   778,   783,   788,   793,   795,   799,
     803,   807,   811,   815,   819,   823,   826,   829,   833,   835,
     839,   843,   847,   851,   855,   859,   863,   866,   869,   873,
     875,   879,   883,   887,   889,   893,   897,   901,   903,   907,
     911,   915,   917,   921,   925,   929,   931,   935,   939,   941,
     944,   947,   949,   953,   957,   961,   963,   967,   971,   975,
     977,   981,   985,   987,   990,   993,   995,   999,  1003,  1007,
    1009,  1013,  1017,  1021,  1023,  1027,  1031,  1033,  1036,  1039,
    1041,  1045,  1049,  1053,  1055,  1059,  1063,  1067,  1069,  1073,
    1077,  1081,  1083,  1087,  1091,  1095,  1097,  1101,  1105,  1109,
    1111,  1115,  1119,  1123,  1125,  1129,  1133,  1137,  1139,  1143,
    1147,  1151,  1155,  1159,  1163,  1167,  1170,  1173,  1177,  1181,
    1185,  1189,  1192,  1198,  1204,  1210,  1216,  1221,  1226,  1232,
    1236,  1238,  1240,  1242,  1244,  1246,  1248,  1250,  1254,  1258,
    1262,  1266,  1270,  1274,  1278,  1281,  1284,  1288,  1292,  1296,
    1300,  1303,  1309,  1315,  1321,  1327,  1332,  1337,  1343,  1347,
    1353,  1359,  1365,  1370,  1375,  1381,  1385,  1387,  1389,  1391,
    1393,  1395,  1397,  1399,  1401,  1405,  1409,  1413,  1415,  1417,
    1419,  1423,  1427,  1431,  1435,  1439,  1441,  1443,  1445,  1447,
    1449,  1452,  1455,  1458,  1460,  1464,  1466,  1471,  1476,  1481,
    1486,  1492,  1498,  1504,  1510,  1512,  1516,  1520,  1524,  1528,
    1532,  1536,  1540,  1543,  1546,  1550,  1552,  1554,  1556,  1560,
    1564,  1568,  1572,  1575,  1578,  1582,  1584,  1588,  1590,  1594,
    1598,  1602,  1606,  1610,  1614,  1618,  1621,  1624,  1632,  1640,
    1648,  1654,  1660,  1666,  1672,  1680,  1686,  1692,  1698,  1704,
    1709,  1715,  1720,  1722,  1724,  1726,  1729,  1732,  1735,  1737,
    1741,  1744,  1746,  1749,  1752,  1755,  1757,  1760,  1763,  1766,
    1768,  1773,  1779,  1781,  1783,  1787,  1791,  1793,  1795,  1797,
    1799,  1801,  1803,  1806,  1809,  1812,  1814,  1817,  1821,  1824,
    1827,  1831,  1835,  1837,  1843,  1849,  1855,  1861,  1867,  1873,
    1879,  1885,  1891,  1897,  1903,  1909,  1915,  1921,  1927,  1933,
    1939,  1945,  1951,  1957,  1963,  1969,  1975,  1981,  1987,  1993,
    1999,  2005,  2011,  2017,  2023,  2029,  2033,  2037,  2041,  2045,
    2049,  2053,  2057,  2060,  2063,  2067,  2070,  2073,  2076,  2079,
    2082,  2085,  2088,  2091,  2094,  2097,  2100,  2103,  2106,  2109,
    2112,  2114,  2118,  2122,  2126,  2130,  2134,  2138,  2142,  2144,
    2146,  2148,  2151,  2154,  2157,  2159,  2163,  2166,  2169,  2173,
    2177,  2179,  2183,  2187,  2191,  2197,  2203,  2209,  2215,  2221,
    2227,  2233,  2239,  2245,  2251,  2257,  2263,  2269,  2275,  2281,
    2287,  2293,  2299,  2305,  2311,  2317,  2323,  2329,  2335,  2341,
    2347,  2353,  2359,  2365,  2371,  2377,  2383,  2387,  2391,  2395,
    2399,  2403,  2407,  2411,  2414,  2417,  2421,  2424,  2427,  2430,
    2433,  2436,  2439,  2442,  2445,  2448,  2451,  2454,  2457,  2460,
    2463,  2466,  2470,  2474,  2478,  2482,  2485,  2487,  2491,  2495,
    2499,  2503,  2507,  2511,  2515
  };

  /* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
  const unsigned short int
  mcmas_parser::yyrline_[] =
  {
         0,   269,   269,   270,   273,   276,   279,   284,   285,   286,
     287,   288,   295,   302,   309,   319,   322,   326,   330,   334,
     337,   341,   345,   350,   357,   364,   371,   378,   385,   392,
     400,   408,   413,   416,   420,   424,   428,   431,   435,   439,
     443,   449,   457,   467,   472,   485,   491,   496,   509,   514,
     519,   535,   540,   545,   550,   563,   569,   575,   581,   585,
     593,   604,   610,   614,   617,   620,   624,   630,   633,   637,
     641,   645,   648,   652,   656,   660,   666,   674,   680,   686,
     692,   695,   699,   703,   707,   710,   714,   718,   723,   729,
     732,   737,   743,   746,   751,   754,   759,   764,   767,   772,
     779,   782,   786,   790,   794,   797,   801,   805,   809,   815,
     821,   828,   835,   839,   845,   849,   852,   861,   877,   882,
     885,   894,   910,   915,   921,   931,   935,   938,   942,   945,
     949,   953,   958,   972,   986,  1000,  1014,  1020,  1023,  1027,
    1031,  1035,  1039,  1043,  1047,  1051,  1054,  1058,  1062,  1066,
    1072,  1075,  1079,  1095,  1111,  1117,  1124,  1127,  1131,  1135,
    1139,  1143,  1147,  1151,  1155,  1158,  1162,  1166,  1170,  1176,
    1182,  1188,  1194,  1198,  1206,  1216,  1222,  1229,  1232,  1236,
    1240,  1244,  1247,  1251,  1255,  1260,  1266,  1274,  1282,  1288,
    1294,  1300,  1308,  1316,  1321,  1328,  1335,  1340,  1347,  1354,
    1359,  1362,  1366,  1370,  1374,  1377,  1381,  1385,  1389,  1395,
    1400,  1406,  1411,  1417,  1423,  1431,  1441,  1447,  1454,  1460,
    1464,  1471,  1478,  1483,  1489,  1495,  1501,  1507,  1512,  1515,
    1520,  1525,  1530,  1536,  1542,  1548,  1554,  1559,  1566,  1571,
    1574,  1579,  1584,  1589,  1595,  1601,  1607,  1613,  1618,  1625,
    1630,  1636,  1642,  1647,  1650,  1656,  1662,  1667,  1670,  1673,
    1678,  1683,  1687,  1693,  1699,  1704,  1707,  1713,  1718,  1721,
    1727,  1732,  1735,  1738,  1743,  1748,  1752,  1758,  1764,  1769,
    1772,  1778,  1783,  1786,  1792,  1797,  1800,  1803,  1808,  1813,
    1817,  1823,  1829,  1834,  1837,  1843,  1848,  1851,  1857,  1862,
    1865,  1868,  1873,  1878,  1882,  1888,  1894,  1899,  1902,  1908,
    1914,  1919,  1922,  1925,  1930,  1935,  1938,  1944,  1950,  1955,
    1958,  1964,  1970,  1975,  1978,  1981,  1986,  1991,  1997,  2000,
    2005,  2010,  2015,  2021,  2027,  2033,  2039,  2044,  2051,  2068,
    2073,  2078,  2083,  2123,  2129,  2135,  2141,  2147,  2153,  2159,
    2165,  2170,  2173,  2176,  2179,  2182,  2185,  2190,  2193,  2198,
    2203,  2208,  2214,  2220,  2226,  2232,  2237,  2244,  2261,  2266,
    2271,  2276,  2307,  2313,  2319,  2325,  2331,  2337,  2343,  2349,
    2366,  2371,  2376,  2381,  2386,  2391,  2396,  2402,  2405,  2415,
    2418,  2421,  2425,  2428,  2438,  2457,  2462,  2467,  2470,  2473,
    2483,  2515,  2521,  2540,  2545,  2550,  2554,  2557,  2567,  2572,
    2575,  2578,  2582,  2586,  2590,  2591,  2595,  2601,  2606,  2611,
    2616,  2624,  2629,  2634,  2639,  2643,  2646,  2651,  2656,  2661,
    2667,  2673,  2678,  2684,  2689,  2696,  2704,  2707,  2711,  2714,
    2718,  2722,  2726,  2730,  2734,  2738,  2742,  2746,  2750,  2753,
    2758,  2763,  2768,  2774,  2780,  2785,  2791,  2796,  2871,  2933,
    2995,  3039,  3046,  3053,  3060,  3108,  3139,  3145,  3151,  3157,
    3163,  3169,  3175,  3182,  3185,  3189,  3192,  3196,  3200,  3204,
    3205,  3206,  3210,  3213,  3217,  3221,  3225,  3228,  3232,  3236,
    3240,  3246,  3254,  3258,  3265,  3274,  3279,  3283,  3286,  3296,
    3303,  3306,  3310,  3313,  3317,  3321,  3325,  3326,  3328,  3332,
    3336,  3340,  3344,  3348,  3354,  3359,  3364,  3369,  3374,  3379,
    3384,  3389,  3402,  3408,  3414,  3420,  3426,  3432,  3438,  3444,
    3450,  3455,  3460,  3465,  3470,  3475,  3480,  3485,  3498,  3504,
    3510,  3516,  3522,  3528,  3534,  3541,  3544,  3549,  3554,  3559,
    3565,  3571,  3576,  3582,  3587,  3593,  3599,  3605,  3611,  3617,
    3623,  3629,  3637,  3645,  3654,  3664,  3674,  3684,  3694,  3700,
    3706,  3721,  3738,  3755,  3768,  3781,  3786,  3791,  3796,  3803,
    3806,  3810,  3813,  3817,  3821,  3825,  3827,  3832,  3836,  3841,
    3845,  3849,  3859,  3864,  3869,  3875,  3880,  3885,  3890,  3895,
    3900,  3905,  3910,  3923,  3929,  3935,  3941,  3947,  3953,  3959,
    3965,  3971,  3976,  3981,  3986,  3991,  3996,  4001,  4006,  4019,
    4025,  4031,  4037,  4043,  4049,  4055,  4062,  4065,  4070,  4075,
    4080,  4086,  4092,  4097,  4103,  4108,  4114,  4120,  4126,  4132,
    4138,  4144,  4150,  4158,  4166,  4175,  4185,  4195,  4205,  4215,
    4219,  4223,  4232,  4241,  4250,  4255,  4270,  4285,  4302,  4319,
    4332,  4345,  4350,  4355,  4360
  };

  // Print the state stack on the debug stream.
  void
  mcmas_parser::yystack_print_ ()
  {
    *yycdebug_ << "Stack now";
    for (state_stack_type::const_iterator i = yystate_stack_.begin ();
	 i != yystate_stack_.end (); ++i)
      *yycdebug_ << ' ' << *i;
    *yycdebug_ << std::endl;
  }

  // Report on the debug stream that the rule \a yyrule is going to be reduced.
  void
  mcmas_parser::yy_reduce_print_ (int yyrule)
  {
    unsigned int yylno = yyrline_[yyrule];
    int yynrhs = yyr2_[yyrule];
    /* Print the symbols being reduced, and their result.  */
    *yycdebug_ << "Reducing stack by rule " << yyrule - 1
	       << " (line " << yylno << "):" << std::endl;
    /* The symbols being reduced.  */
    for (int yyi = 0; yyi < yynrhs; yyi++)
      YY_SYMBOL_PRINT ("   $" << yyi + 1 << " =",
		       yyrhs_[yyprhs_[yyrule] + yyi],
		       &(yysemantic_stack_[(yynrhs) - (yyi + 1)]),
		       &(yylocation_stack_[(yynrhs) - (yyi + 1)]));
  }
#endif // YYDEBUG

  /* YYTRANSLATE(YYLEX) -- Bison symbol number corresponding to YYLEX.  */
  mcmas_parser::token_number_type
  mcmas_parser::yytranslate_ (int t)
  {
    static
    const token_number_type
    translate_table[] =
    {
           0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,    61,    62,    63,    64,
      65,    66,    67,    68,    69,    70,    71,    72,    73
    };
    if ((unsigned int) t <= yyuser_token_number_max_)
      return translate_table[t];
    else
      return yyundef_token_;
  }

  const int mcmas_parser::yyeof_ = 0;
  const int mcmas_parser::yylast_ = 7285;
  const int mcmas_parser::yynnts_ = 124;
  const int mcmas_parser::yyempty_ = -2;
  const int mcmas_parser::yyfinal_ = 16;
  const int mcmas_parser::yyterror_ = 1;
  const int mcmas_parser::yyerrcode_ = 256;
  const int mcmas_parser::yyntokens_ = 74;

  const unsigned int mcmas_parser::yyuser_token_number_max_ = 328;
  const mcmas_parser::token_number_type mcmas_parser::yyundef_token_ = 2;


} // yy

/* Line 1136 of lalr1.cc  */
#line 11620 "parser/nssis.cc"


/* Line 1138 of lalr1.cc  */
#line 4365 "parser/nssis_new.yy"

void
yy::mcmas_parser::error (const yy::mcmas_parser::location_type& l,
                          const std::string& m)
{
  driver.error (l, m);
}

