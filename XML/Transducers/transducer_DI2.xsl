<?xml version="1.0" encoding="utf-8"?>
<!-- Content generated automatically -->
<xsl:stylesheet 
    xmlns=""
    xmlns:xs="http://www.w3.org/2001/XMLSchema"
    xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
    version="2.0"
    exclude-result-prefixes="xs">
    
  <xsl:output method="xml" encoding="utf-8" indent="yes"/>
  
  <xsl:template match="/tree">
    <xsl:text disable-output-escaping="yes">
&lt;!DOCTYPE tree SYSTEM "tree.dtd"&gt;
</xsl:text>
    <tree>
      <xsl:apply-templates select="signature"/>
      <xsl:apply-templates select="node" mode="axiom"/>
    </tree>
  </xsl:template>  

  <xsl:template match="signature">
    <signature>
      <symbol name="a" arity="0"/>
      <symbol name="b" arity="0"/>
    </signature>
  </xsl:template>

  <xsl:template match="node" mode="axiom">
    <xsl:apply-templates select="." mode="q1"/>
  </xsl:template>

  <xsl:template match="node[@symbol='u']" mode="q1">
    <xsl:apply-templates select="node[1]" mode="q1"/>

  </xsl:template>

  <xsl:template match="node[@symbol='a']" mode="q1">
    <node symbol="a">
    </node>
  </xsl:template>

  <xsl:template match="node[@symbol='b']" mode="q1">
    <node symbol="b">
    </node>
  </xsl:template>

  <xsl:template match="node[@symbol='f']" mode="q1">
    <xsl:apply-templates select="node[1]" mode="q1"/>

  </xsl:template>

</xsl:stylesheet>