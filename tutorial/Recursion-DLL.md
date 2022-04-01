---
title: JML Tutorial - Reasoning about recursive functions and data structures (doubly-linked list with model fields version)
---
<i>Last Modified: <script type="text/javascript"> document.write(new Date(document.lastModified).toUTCString())</script></i>

This example extends the [lesson about recursion](Recursion) with doubly-linked list example, also using model fields.
Along with the extra reference manipulation for the back pointers, note the use of the `goodLinksForward` method to establish the well-formedness of the list pointers.

```
{% include_relative ListDLL.java %}
```
 
