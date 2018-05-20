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
      <symbol name="a" arity="1"/>
      <symbol name="b" arity="1"/>
      <symbol name="#" arity="0"/>
    </signature>
  </xsl:template>

  <xsl:template match="node" mode="axiom">
    <xsl:apply-templates select="." mode="q0"/>
  </xsl:template>

  <xsl:template match="node[@symbol='f']" mode="q0">
    <xsl:apply-templates select="node[1]" mode="q0"/>

  </xsl:template>

  <xsl:template match="node[@symbol='a']" mode="q0">
    <node symbol="a">
    <xsl:apply-templates select="node[1]" mode="q0"/>
    </node>
  </xsl:template>

  <xsl:template match="node[@symbol='b']" mode="q0">
    <node symbol="b">
    <xsl:apply-templates select="node[1]" mode="q0"/>
    </node>
  </xsl:template>

  <xsl:template match="node[@symbol='#']" mode="q0">
    <node symbol="#">
    </node>
  </xsl:template>

</xsl:stylesheet>