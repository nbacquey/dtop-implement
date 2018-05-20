<?xml version="1.0" encoding="utf-8"?>
<xsl:stylesheet
    xmlns=""
    xmlns:xs="http://www.w3.org/2001/XMLSchema"
    xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
    version="2.0"
    exclude-result-prefixes="xs">
    
  <xsl:output method="xml" encoding="utf-8" indent="yes"/>

  <xsl:template match="/transducer">
  
    <xsl:text disable-output-escaping="yes">
&lt;!-- Content generated automatically --&gt;
&lt;xsl:stylesheet 
    xmlns=""
    xmlns:xs="http://www.w3.org/2001/XMLSchema"
    xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
    version="2.0"
    exclude-result-prefixes="xs"&gt;
    
  &lt;xsl:output method="xml" encoding="utf-8" indent="yes"/&gt;
  
  &lt;xsl:template match="/tree"&gt;
    &lt;xsl:text disable-output-escaping="yes"&gt;
&amp;lt;!DOCTYPE tree SYSTEM "tree.dtd"&amp;gt;
&lt;/xsl:text&gt;
    &lt;tree&gt;
      &lt;xsl:apply-templates select="signature"/&gt;
      &lt;xsl:apply-templates select="node" mode="axiom"/&gt;
    &lt;/tree&gt;
  &lt;/xsl:template&gt;  
</xsl:text>

    <xsl:apply-templates select="signature-out"/>
    
    <xsl:apply-templates select="axiom"/>
    
    <xsl:apply-templates select="rules"/>

    <xsl:text disable-output-escaping="yes">
&lt;/xsl:stylesheet&gt;</xsl:text>

  </xsl:template>
  
  <xsl:template match="signature-out">
    <xsl:text disable-output-escaping="yes">
  &lt;xsl:template match="signature"&gt;
    &lt;signature&gt;</xsl:text>

    <xsl:apply-templates select="symbol"/>

    <xsl:text disable-output-escaping="yes">
    &lt;/signature>
  &lt;/xsl:template>
</xsl:text>
  </xsl:template>
  
  <xsl:template match="symbol">
    <xsl:text>
&#032;&#032;&#032;&#032;&#032;&#032;</xsl:text>
    <xsl:copy-of select="."/>
  </xsl:template>

  <xsl:template match="axiom">
    <xsl:text disable-output-escaping="yes">
  &lt;xsl:template match="node" mode="axiom"&gt;
</xsl:text>
    
    <xsl:apply-templates select="context | call" mode="axiom"/>  
    
    <xsl:text disable-output-escaping="yes">  &lt;/xsl:template&gt;
</xsl:text>

  </xsl:template>
  
  <xsl:template match="rules">
    <xsl:apply-templates select="rule"/>
  </xsl:template>
  
  <xsl:template match="rule">
    <xsl:text disable-output-escaping ="yes">
  &lt;xsl:template match="node[@symbol='</xsl:text>
    <xsl:value-of select="@symbol"/>
    <xsl:text disable-output-escaping="yes">']" mode="q</xsl:text>
    <xsl:value-of select="@state"/>
    <xsl:text disable-output-escaping="yes">"&gt;
</xsl:text>

    <xsl:apply-templates select="context | call"/>
    
    <xsl:text disable-output-escaping="yes">
  &lt;/xsl:template&gt;
</xsl:text>
      
  </xsl:template>
  
  <xsl:template match="context">
    <xsl:text disable-output-escaping="yes">    &lt;node symbol="</xsl:text>
    <xsl:value-of select="@symbol"/>
    <xsl:text disable-output-escaping="yes">"&gt;
</xsl:text>

    <xsl:apply-templates select="context | call"/>
    
    <xsl:text disable-output-escaping="yes">    &lt;/node&gt;</xsl:text>    
  </xsl:template>
  
  <xsl:template match="call">
    <xsl:text disable-output-escaping="yes">    &lt;xsl:apply-templates select="node[</xsl:text>
    <xsl:value-of select="@variable"/>
    <xsl:text disable-output-escaping="yes">]" mode="q</xsl:text>
    <xsl:value-of select="@state"/>
    <xsl:text disable-output-escaping="yes">"/&gt;
</xsl:text>
  </xsl:template>
  
  <xsl:template match="context" mode="axiom">
    <xsl:text disable-output-escaping="yes">    &lt;node symbol="</xsl:text>
    <xsl:value-of select="@symbol"/>
    <xsl:text disable-output-escaping="yes">"&gt;
</xsl:text>

    <xsl:apply-templates select="context | call" mode="axiom"/>
    
    <xsl:text disable-output-escaping="yes">    &lt;/node&gt;</xsl:text>    
  </xsl:template>
  
  <xsl:template match="call" mode="axiom">
    <xsl:text disable-output-escaping="yes">    &lt;xsl:apply-templates select="." mode="q</xsl:text>
    <xsl:value-of select="@state"/>
    <xsl:text disable-output-escaping="yes">"/&gt;
</xsl:text>
  </xsl:template>
  
</xsl:stylesheet>